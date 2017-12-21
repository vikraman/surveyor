{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Surveyor ( surveyor ) where

import qualified Brick as B
import qualified Brick.BChan as B
import qualified Brick.Widgets.Border.Style as B
import qualified Brick.Widgets.List as B
import qualified Control.Lens as L
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Monoid
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TE
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Traversable as T
import qualified Data.Vector as V
import qualified Graphics.Vty as V
import           Text.Printf ( printf )

import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Renovate as R

import           Surveyor.BinaryAnalysisResult ( BinaryAnalysisResult(..)
                                               , BinaryAnalysisResultWrapper(..)
                                               )
import           Surveyor.Events ( Events(..) )
import           Surveyor.Loader ( asynchronouslyLoad )

data State where
  State :: (MM.MemWidth w) => S i a w arch -> State

data S i a w arch =
  S { sInputFile :: Maybe FilePath
    , sBinaryInfo :: Maybe (BinaryAnalysisResult i a w arch)
    , sDiagnosticLog :: Seq.Seq T.Text
    , sUIMode :: UIMode
    , sFunctionList :: B.List Names (FunctionListEntry w)
    }

data FunctionListEntry w = FLE (R.ConcreteAddress w) T.Text Int

data UIMode = Diags
            -- ^ A window containing the history of diagnostic information
            | Summary
            -- ^ Summary information returned by the binary analysis
            | ListFunctions
            -- ^ A list of all of the discovered functions (which allows for
            -- drilling down and displaying blocks)
            deriving (Eq, Ord, Show)

data Names = DiagnosticView
           | DiagnosticContent
           | FunctionList
  deriving (Eq, Ord, Show)

drawSummary :: FilePath -> BinaryAnalysisResult i a w arch -> B.Widget Names
drawSummary binFileName BinaryAnalysisResult { rBlockInfo = binfo } =
  B.vBox [ B.str ("Target binary: " ++ binFileName)
         , B.str ("Discovered functions: " ++ show (length (R.biFunctionEntries binfo)))
         , B.str ("Discovered blocks: " ++ show (length (R.biBlocks binfo)))
         ]

drawConcreteBlock :: (MM.MemWidth w) => R.ISA i a w -> R.ConcreteBlock i w -> B.Widget Names
drawConcreteBlock isa b =
  B.vBox [ B.str (printf "Block address: %s" (show (R.basicBlockAddress b)))
         , B.vBox [ B.str (R.isaPrettyInstruction isa i) | i <- R.basicBlockInstructions b ]
         ]

drawFunctionList :: (MM.MemWidth w) => S i a w arch -> BinaryAnalysisResult i a w arch -> B.Widget Names
drawFunctionList S { sFunctionList = flist }
                 BinaryAnalysisResult { rBlockInfo = binfo, rISA = isa } =
  B.renderList drawFunctionEntry True flist
  where
    drawFunctionEntry isFocused (FLE addr txt blockCount) =
      let focusedXfrm = if isFocused then B.withAttr "focused" else id
      in focusedXfrm (B.hBox [B.str (printf "%s: %s (%d blocks)" (show (PP.pretty addr)) (T.unpack txt) blockCount)])

drawDiagnostics :: Seq.Seq T.Text -> B.Widget Names
drawDiagnostics diags = B.viewport DiagnosticView B.Vertical body
  where
    body = B.vBox [ B.txtWrap t | t <- F.toList diags ]

contained :: B.Widget Names -> B.Widget Names
contained = B.withBorderStyle B.unicodeRounded

appDraw :: State -> [B.Widget Names]
appDraw (State s) =
  case sInputFile s of
    Nothing -> [contained (B.txt "No file loaded")]
    Just binFileName ->
      case sBinaryInfo s of
        Nothing -> [contained (B.str ("Analyzing " ++ binFileName))]
        Just binfo ->
          case sUIMode s of
            Diags -> [contained (drawDiagnostics (sDiagnosticLog s))]
            Summary -> [contained (drawSummary binFileName binfo)]
            ListFunctions -> [contained (drawFunctionList s binfo)]

appChooseCursor :: State -> [B.CursorLocation Names] -> Maybe (B.CursorLocation Names)
appChooseCursor _ _ = Nothing

appHandleEvent :: State -> B.BrickEvent Names Events -> B.EventM Names (B.Next State)
appHandleEvent (State s0) evt =
  case evt of
    B.AppEvent ae ->
      case ae of
        AnalysisFinished (BinaryAnalysisResultWrapper bar@BinaryAnalysisResult { rBlockInfo = rbi }) diags ->
          let newDiags = map (\d -> T.pack ("Analysis: " ++ show d)) diags
              notification = "Finished loading file"
              funcList = V.fromList [ FLE addr textName blockCount
                                    | (addr, Some dfi) <- M.toList (R.biDiscoveryFunInfo rbi)
                                    , let textName = TE.decodeUtf8With TE.lenientDecode (MD.discoveredFunName dfi)
                                    , let blockCount = M.size (dfi L.^. MD.parsedBlocks)
                                    ]
          in B.continue $ State S { sBinaryInfo = Just bar
                                  , sFunctionList = B.list FunctionList funcList 1
                                  , sDiagnosticLog =
                                    sDiagnosticLog s0 <> Seq.fromList newDiags <> Seq.singleton notification
                                  , sUIMode = Diags
                                  , sInputFile = sInputFile s0
                                  }
        AnalysisProgress _addr (BinaryAnalysisResultWrapper bar@BinaryAnalysisResult { rBlockInfo = rbi }) ->
          let funcList = V.fromList [ FLE addr textName blockCount
                                    | (addr, Some dfi) <- M.toList (R.biDiscoveryFunInfo rbi)
                                    , let textName = TE.decodeUtf8With TE.lenientDecode (MD.discoveredFunName dfi)
                                    , let blockCount = M.size (dfi L.^. MD.parsedBlocks)
                                    ]
          in B.continue $ State S { sBinaryInfo = Just bar
                                  , sFunctionList = B.list FunctionList funcList 1
                                  , sDiagnosticLog = sDiagnosticLog s0
                                  , sUIMode = sUIMode s0
                                  , sInputFile = sInputFile s0
                                  }
        BlockDiscovered addr ->
          B.continue $ State s0 { sDiagnosticLog = sDiagnosticLog s0 Seq.|> T.pack ("Found a block at address " ++ show addr) }
        AnalysisFailure exn ->
          B.continue $ State s0 { sDiagnosticLog = sDiagnosticLog s0 Seq.|> T.pack ("Analysis failure: " ++ show exn) }
        ErrorLoadingELFHeader off msg ->
          let t = T.pack (printf "ELF Loading error at offset 0x%x: %s" off msg)
          in B.continue $ State s0 { sDiagnosticLog = sDiagnosticLog s0 Seq.|> t }
        ErrorLoadingELF errs ->
          let newDiags = map (\d -> T.pack (printf "ELF Loading error: %s" (show d))) errs
          in B.continue $ State s0 { sDiagnosticLog = sDiagnosticLog s0 <> Seq.fromList newDiags }
    B.VtyEvent vtyEvt -> handleVtyEvent (State s0) vtyEvt
    B.MouseDown {} -> B.continue (State s0)
    B.MouseUp {} -> B.continue (State s0)

isListEventKey :: V.Key -> Bool
isListEventKey k =
  case k of
    V.KUp -> True
    V.KDown -> True
    V.KHome -> True
    V.KEnd -> True
    V.KPageDown -> True
    V.KPageUp -> True
    _ -> False

handleVtyEvent :: State -> V.Event -> B.EventM Names (B.Next State)
handleVtyEvent s0@(State (s@S { sFunctionList = l0 })) evt =
  case evt of
    V.EvKey (V.KChar 's') [] ->
      B.continue $ State (s { sUIMode = Summary })
    V.EvKey (V.KChar 'm') [] ->
      B.continue $ State (s { sUIMode = Diags })
    V.EvKey (V.KChar 'f') [] ->
      B.continue $ State (s { sUIMode = ListFunctions })
    V.EvKey (V.KChar 'q') [] -> B.halt s0
    V.EvKey V.KEsc [] -> B.halt s0
    V.EvKey k []
      | sUIMode s == ListFunctions && isListEventKey k -> do
          l1 <- B.handleListEvent evt l0
          B.continue (State (s { sFunctionList = l1 }))
    _ -> B.continue s0

appStartEvent :: State -> B.EventM Names State
appStartEvent s0 = return s0

appAttrMap :: State -> B.AttrMap
appAttrMap _ = B.attrMap V.defAttr [ ("focused", B.bg V.blue)
                                   ]

surveyor :: Maybe FilePath -> IO ()
surveyor mExePath = do
  customEventChan <- B.newBChan 100
  let app = B.App { B.appDraw = appDraw
                  , B.appChooseCursor = appChooseCursor
                  , B.appHandleEvent = appHandleEvent
                  , B.appStartEvent = appStartEvent
                  , B.appAttrMap = appAttrMap
                  }
  _ <- T.traverse (asynchronouslyLoad customEventChan) mExePath
  let initialState = State S { sInputFile = mExePath
                           , sBinaryInfo = Nothing
                           , sDiagnosticLog = Seq.empty
                           , sFunctionList = (B.list FunctionList (V.empty @(FunctionListEntry 64)) 1)
                           , sUIMode = Diags
                           }
  _finalState <- B.customMain (V.mkVty V.defaultConfig) (Just customEventChan) app initialState
  return ()

