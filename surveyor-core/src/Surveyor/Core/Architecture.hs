{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- | Abstractions over program representations
--
-- These definitions are designed to allow the Surveyor UI to abstractly handle
-- different architectures, building up abstractions over functions, blocks,
-- instructions, and operands.
module Surveyor.Core.Architecture (
  ArchConstraints,
  IR(..),
  SomeIRRepr(..),
  Architecture(..),
  SymbolicArchitecture(..),
  CruciblePersonality,
  AnalysisResult,
  Block(..),
  FunctionHandle(..),
  BlockMapping(..),
  ParameterizedFormula(..),
  prettyParameterizedFormula,
  SomeResult(..),
  MC.mkPPC32Result,
  MC.mkPPC64Result,
  MC.mkX86Result,
  J.mkInitialJVMResult,
  J.extendJVMResult,
  LL.LLVM,
  LL.LLVMPersonality(..),
  LL.llvmAnalysisResultFromModule,
  LL.mkLLVMResult,
  M.Macaw,
  ) where

import           Surveyor.Core.Architecture.Class
import qualified Surveyor.Core.Architecture.JVM as J
import qualified Surveyor.Core.Architecture.LLVM as LL
import qualified Surveyor.Core.Architecture.MC as MC
import qualified Surveyor.Core.Architecture.Macaw as M
import           Surveyor.Core.Architecture.Void ()
