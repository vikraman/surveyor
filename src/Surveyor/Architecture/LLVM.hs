-- | An implementation of 'Architecture' for LLVM bitcode
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Surveyor.Architecture.LLVM ( mkLLVMResult ) where

import           Control.Monad ( guard )
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import           Data.Maybe ( fromMaybe, mapMaybe )
import qualified Data.Parameterized.Nonce as NG
import qualified Data.Text as T
import qualified Text.LLVM as LL
import qualified Text.LLVM.PP as LL
import qualified Text.PrettyPrint as PP
import           Text.Printf ( printf )

import           Surveyor.Architecture.Class

data LLVM

data LLVMResult s =
  LLVMResult { llvmNonce :: NG.Nonce s LLVM
             , llvmModule :: LL.Module
             , llvmFunctionIndex :: FunctionIndex
             }

type FunctionIndex = M.Map LL.Symbol (LL.Define, BlockIndex)
type BlockIndex = M.Map (Maybe LL.BlockLabel) LL.BasicBlock

indexFunctions :: LL.Module -> FunctionIndex
indexFunctions = F.foldl' indexDefine M.empty . LL.modDefines
  where
    indexDefine m def
      | null (LL.defBody def) = m
      | otherwise  =
        let blockIndex = F.foldl' indexBlock M.empty (LL.defBody def)
        in M.insert (LL.defName def) (def, blockIndex) m
    indexBlock m b = M.insert (LL.bbLabel b) b m

mkLLVMResult :: NG.Nonce s LLVM -> LL.Module -> SomeResult s
mkLLVMResult nonce m =
  SomeResult (LLVMAnalysisResult lr)
  where
    lr = LLVMResult { llvmNonce = nonce
                    , llvmModule = m
                    , llvmFunctionIndex = indexFunctions m
                    }

-- | The type of an LLVM address
--
-- There isn't really an address type. Blocks have BlockLabels and the name of
-- the containing function, while instructions can be addressed by tuples of
-- (Symbol, BlockLabel, Int) where the Int is an offset into the block.
-- Function addresses are just names, since they have to be unique.  For names,
-- we use the LLVM symbols associated with them, which are uniqued strings.
data Addr = FunctionAddr !LL.Symbol
          | BlockAddr !LL.Symbol (Maybe LL.BlockLabel)
          | InsnAddr !LL.Symbol (Maybe LL.BlockLabel) !Int
          deriving (Eq, Ord)

data LLVMOperand' = Value !LL.Value
                  | TypedValue !(LL.Typed LL.Value)
                  | Type !LL.Type
                  | ConstantInt !Int
                  | BlockLabel !LL.BlockLabel
                  | ConstantString String
                  | SwitchTarget LL.Type (Integer, LL.BlockLabel)

instance Architecture LLVM s where
  data AnalysisResult LLVM s = LLVMAnalysisResult (LLVMResult s)
  data Instruction LLVM s = LLVMInstruction LL.Stmt
  data Operand LLVM s = LLVMOperand LLVMOperand'
  data Opcode LLVM s = LLVMOpcode LL.Instr
  data Address LLVM s = LLVMAddress Addr
  archNonce (LLVMAnalysisResult lr) = llvmNonce lr
  genericSemantics _ _ = Nothing
  boundValue (LLVMInstruction stmt) =
    case stmt of
      LL.Result iden _ _ -> Just (LLVMOperand (Value (LL.ValIdent iden)))
      LL.Effect {} -> Nothing
  prettyOperand (LLVMAddress _addr) (LLVMOperand val) =
    let ?config = llvmConfig
    in T.pack (show (ppOperand val)) -- T.pack (show (LL.ppValue val))
  prettyAddress (LLVMAddress addr) =
    case addr of
      FunctionAddr (LL.Symbol name) -> T.pack name
      BlockAddr (LL.Symbol name) l -> T.pack (printf "%s%s" name (maybe "" (("@"++) . show . LL.ppLabel) l))
      InsnAddr (LL.Symbol name) l i -> T.pack (printf "%s%s:%d" name (maybe "" (("@"++) . show . LL.ppLabel) l) i)
  -- Will work on what this means - we can probably do something if we also pass
  -- in the analysisresult
  parseAddress _ = Nothing
  prettyInstruction _ (LLVMInstruction stmt) =
    let ?config = llvmConfig
    in T.pack (show (LL.ppStmt stmt))
  opcode (LLVMInstruction stmt) =
    case stmt of
      LL.Result _ i _ -> LLVMOpcode i
      LL.Effect i _ -> LLVMOpcode i
  functions (LLVMAnalysisResult lr) =
    mapMaybe defToFunction (LL.modDefines (llvmModule lr))
  prettyOpcode (LLVMOpcode i) = ppOpcode i
  operands (LLVMInstruction stmt) = stmtOperands stmt
  containingBlocks (LLVMAnalysisResult lr) (LLVMAddress addr) =
    llvmContainingBlocks lr addr
  summarizeResult (LLVMAnalysisResult lr) =
    summarizeModule (llvmModule lr)
  functionBlocks (LLVMAnalysisResult lr) fh =
    llvmFunctionBlocks lr fh

instance Eq (Address LLVM s) where
  LLVMAddress a1 == LLVMAddress a2 = a1 == a2

instance Ord (Address LLVM s) where
  compare (LLVMAddress a1) (LLVMAddress a2) = compare a1 a2

ppOperand :: (?config :: LL.Config) => LLVMOperand' -> PP.Doc
ppOperand op =
  case op of
    Value v -> LL.ppValue v
    TypedValue tv -> LL.ppTyped LL.ppValue tv
    Type ty -> LL.ppType ty
    ConstantInt i -> PP.int i
    BlockLabel l -> LL.ppLabel l
    ConstantString s -> PP.text s
    SwitchTarget t (val, target) -> LL.ppSwitchEntry t (val, target)

stmtOperands :: LL.Stmt -> [Operand LLVM s]
stmtOperands stmt =
  case stmt of
    LL.Result _ instr _ -> instrOperands instr
    LL.Effect instr _ -> instrOperands instr

instrOperands :: LL.Instr -> [Operand LLVM s]
instrOperands i =
  case i of
    LL.RetVoid {} -> []
    LL.Ret rv -> [LLVMOperand (TypedValue rv)]
    LL.Arith _ tv v -> [ LLVMOperand (TypedValue tv)
                       , LLVMOperand (Value v)
                       ]
    LL.Bit _ tv v -> [ LLVMOperand (TypedValue tv)
                     , LLVMOperand (Value v)
                     ]
    LL.Conv _ tv ty -> [ LLVMOperand (TypedValue tv)
                       , LLVMOperand (Type ty)
                       ]
    LL.Call _ ty callee args ->
      LLVMOperand (Type ty) : LLVMOperand (Value callee) : map (LLVMOperand . TypedValue) args
    LL.Alloca ty nelts align ->
      concat [ [LLVMOperand (Type ty)]
             , maybe [] ((:[]) . LLVMOperand . TypedValue) nelts
             , maybe [] ((:[]) . LLVMOperand . ConstantInt) align
             ]
    LL.Load tv align ->
      concat [ [LLVMOperand (TypedValue tv)]
             , maybe [] ((:[]) . LLVMOperand . ConstantInt) align
             ]
    LL.Store tv1 tv2 align ->
      concat [ [LLVMOperand (TypedValue tv1), LLVMOperand (TypedValue tv2)]
             , maybe [] ((:[]) . LLVMOperand . ConstantInt) align
             ]
    LL.ICmp _ tv v -> [LLVMOperand (TypedValue tv), LLVMOperand (Value v)]
    LL.FCmp _ tv v -> [LLVMOperand (TypedValue tv), LLVMOperand (Value v)]
    LL.Phi ty vs -> LLVMOperand (Type ty) : map (LLVMOperand . Value . fst) vs
    LL.GEP _ tv tvs -> LLVMOperand (TypedValue tv) : map (LLVMOperand . TypedValue) tvs
    LL.Select tv1 tv2 v -> [ LLVMOperand (TypedValue tv1)
                           , LLVMOperand (TypedValue tv2)
                           , LLVMOperand (Value v)
                           ]
    LL.ExtractValue tv ixs -> LLVMOperand (TypedValue tv) : map (LLVMOperand . ConstantInt . fromIntegral) ixs
    LL.InsertValue tv1 tv2 ixs ->
      LLVMOperand (TypedValue tv1) : LLVMOperand (TypedValue tv2) : map (LLVMOperand . ConstantInt . fromIntegral) ixs
    LL.ExtractElt tv v -> [LLVMOperand (TypedValue tv), LLVMOperand (Value v)]
    LL.InsertElt tv1 tv2 v -> [ LLVMOperand (TypedValue tv1)
                              , LLVMOperand (TypedValue tv2)
                              , LLVMOperand (Value v)
                              ]
    LL.ShuffleVector tv1 v tv2 -> [ LLVMOperand (TypedValue tv1)
                                  , LLVMOperand (Value v)
                                  , LLVMOperand (TypedValue tv2)
                                  ]
    LL.Jump lab -> [ LLVMOperand (BlockLabel lab) ]
    LL.Br tv l1 l2 -> [ LLVMOperand (TypedValue tv)
                      , LLVMOperand (BlockLabel l1)
                      , LLVMOperand (BlockLabel l2)
                      ]
    LL.Invoke ty v tvs l1 l2 ->
      concat [ [LLVMOperand (Type ty), LLVMOperand (Value v)]
             , map (LLVMOperand . TypedValue) tvs
             , [ LLVMOperand (BlockLabel l1), LLVMOperand (BlockLabel l2) ]
             ]
    LL.Comment s -> [ LLVMOperand (ConstantString s) ]
    LL.Unreachable -> []
    LL.Unwind -> []
    LL.VaArg tv t -> [ LLVMOperand (TypedValue tv), LLVMOperand (Type t) ]
    LL.IndirectBr tv labs ->
      LLVMOperand (TypedValue tv) : map (LLVMOperand . BlockLabel) labs
    LL.Switch tv lab cases ->
      let ty = LL.typedType tv
      in LLVMOperand (TypedValue tv) : LLVMOperand (BlockLabel lab) : map (LLVMOperand . SwitchTarget ty) cases
    LL.LandingPad ty tv _ _ -> [ LLVMOperand (Type ty)
                               , LLVMOperand (TypedValue tv)
                               ]
    LL.Resume tv -> [ LLVMOperand (TypedValue tv) ]

summarizeModule :: LL.Module -> [(T.Text, T.Text)]
summarizeModule m =
  [ ("Data Layout", T.pack (show (LL.ppDataLayout (LL.modDataLayout m))))
  , ("# Globals", T.pack (show (length (LL.modGlobals m))))
  , ("# Aliases", T.pack (show (length (LL.modAliases m))))
  ]

ppOpcode :: LL.Instr -> T.Text
ppOpcode i =
  case i of
    LL.Ret {} -> "ret"
    LL.RetVoid -> "ret"
    LL.Call False _ _ _ -> "call"
    LL.Call True _ _ _ -> "call tail"
    LL.Invoke {} -> "invoke"
    LL.Alloca {} -> "alloca"
    LL.Load {} -> "load"
    LL.Store {} -> "store"
    LL.ICmp {} -> "icmp"
    LL.FCmp {} -> "fcmp"
    LL.Phi {} -> "phi"
    LL.GEP False _ _ -> "getelementptr"
    LL.GEP True _ _ -> "getelementptr inbounds"
    LL.Select {} -> "select"
    LL.ExtractValue {} -> "extractvalue"
    LL.InsertValue {} -> "insertvalue"
    LL.ExtractElt {} -> "extractelement"
    LL.InsertElt {} -> "insertelement"
    LL.ShuffleVector {} -> "shufflevector"
    LL.Jump {} -> "jump"
    LL.Br {} -> "br"
    LL.Comment {} -> "comment"
    LL.Unreachable {} -> "unreachable"
    LL.Unwind {} -> "unwind"
    LL.VaArg {} -> "va_arg"
    LL.IndirectBr {} -> "indirectbr"
    LL.Switch {} -> "switch"
    LL.LandingPad {} -> "landingpad"
    LL.Resume {} -> "resume"
    LL.Arith LL.FAdd _ _ -> "fadd"
    LL.Arith LL.FSub _ _ -> "fsub"
    LL.Arith LL.FMul _ _ -> "fmul"
    LL.Arith LL.FDiv _ _ -> "fdiv"
    LL.Arith LL.URem _ _ -> "urem"
    LL.Arith LL.SRem _ _ -> "srem"
    LL.Arith LL.FRem _ _ -> "frem"
    LL.Arith (LL.Add nuw nsw) _ _ -> binOverflow "add" nuw nsw
    LL.Arith (LL.Sub nuw nsw) _ _ -> binOverflow "sub" nuw nsw
    LL.Arith (LL.Mul nuw nsw) _ _ -> binOverflow "mul" nuw nsw
    LL.Arith (LL.UDiv exact) _ _ -> binExact "udiv" exact
    LL.Arith (LL.SDiv exact) _ _ -> binExact "sdiv" exact
    LL.Bit (LL.Shl nuw nsw) _ _ -> binOverflow "shl" nuw nsw
    LL.Bit (LL.Lshr exact) _ _ -> binExact "lshr" exact
    LL.Bit (LL.Ashr exact) _ _ -> binExact "ashr" exact
    LL.Bit LL.And _ _ -> "and"
    LL.Bit LL.Or _ _ -> "or"
    LL.Bit LL.Xor _ _ -> "xor"
    LL.Conv LL.Trunc _ _ -> "trunc"
    LL.Conv LL.ZExt _ _ -> "zext"
    LL.Conv LL.SExt _ _ -> "sext"
    LL.Conv LL.FpTrunc _ _ -> "fptrunc"
    LL.Conv LL.FpExt _ _ -> "fpext"
    LL.Conv LL.FpToUi _ _ -> "fptoui"
    LL.Conv LL.FpToSi _ _ -> "fptosi"
    LL.Conv LL.UiToFp _ _ -> "uitofp"
    LL.Conv LL.SiToFp _ _ -> "uitosp"
    LL.Conv LL.PtrToInt _ _ -> "ptrtoint"
    LL.Conv LL.IntToPtr _ _ -> "inttoptr"
    LL.Conv LL.BitCast _ _ -> "bitcast"

binExact :: String -> Bool -> T.Text
binExact opc exact =
  T.pack (printf "%s%s" opc exact')
  where
    exact' :: String
    exact' = if exact then " exact" else ""

binOverflow :: String -> Bool -> Bool -> T.Text
binOverflow opc nuw nsw =
  T.pack (printf "%s%s%s" opc nuw' nsw')
  where
    nuw' :: String
    nuw' = if nuw then " nuw" else ""
    nsw' :: String
    nsw' = if nsw then " nsw" else ""

defToFunction :: LL.Define -> Maybe (FunctionHandle LLVM s)
defToFunction def = do
  guard (not (null (LL.defBody def)))
  let sym@(LL.Symbol str) = LL.defName def
  return $! FunctionHandle { fhAddress = LLVMAddress (FunctionAddr sym)
                           , fhName = T.pack str
                           }

llvmConfig :: LL.Config
llvmConfig = LL.Config { LL.cfgLoadImplicitType = True
                       , LL.cfgGEPImplicitType = True
                       , LL.cfgUseDILocation = False
                       }

llvmContainingBlocks :: LLVMResult s -> Addr -> [Block LLVM s]
llvmContainingBlocks lr addr =
  case addr of
    FunctionAddr _ -> []
    BlockAddr sym lab -> fromMaybe [] $ do
      (_, bix) <- M.lookup sym (llvmFunctionIndex lr)
      bb <- M.lookup lab bix
      return [toBlock sym bb]
    InsnAddr sym lab _ -> fromMaybe [] $ do
      (_, bix) <- M.lookup sym (llvmFunctionIndex lr)
      bb <- M.lookup lab bix
      return [toBlock sym bb]

llvmFunctionBlocks :: LLVMResult s -> FunctionHandle LLVM s -> [Block LLVM s]
llvmFunctionBlocks lr fh =
  case M.lookup sym (llvmFunctionIndex lr) of
    Nothing -> []
    Just (def, _) -> map (toBlock sym) (LL.defBody def)
  where
    sym = LL.Symbol (T.unpack (fhName fh))

toBlock :: LL.Symbol -> LL.BasicBlock -> Block LLVM s
toBlock sym b =
  Block { blockAddress = LLVMAddress (BlockAddr sym lab)
        , blockInstructions = map (toInstruction sym lab) (zip [0..] (LL.bbStmts b))
        }
  where
    lab = LL.bbLabel b

toInstruction :: LL.Symbol -> Maybe LL.BlockLabel -> (Int, LL.Stmt) -> (Address LLVM s, Instruction LLVM s)
toInstruction sym lab (idx, stmt) = (LLVMAddress (InsnAddr sym lab idx), LLVMInstruction stmt)

