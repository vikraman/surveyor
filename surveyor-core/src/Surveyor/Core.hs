{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Surveyor.Core (
  -- * Channel abstraction
  CS.Chan,
  CS.mkChan,
  CS.readChan,
  CS.writeChan,
  -- * Events
  CE.Events(..),
  CE.EventExtension,
  CE.ContextEvent(..),
  CE.LoggingEvent(..),
  CE.LoadEvent(..),
  CE.InfoEvent(..),
  CE.SymbolicExecutionEvent(..),
  CE.ToEvent(..),
  CE.emitEvent,
  -- * Binaries
  -- ** Loading
  CL.AsyncLoader,
  CL.cancelLoader,
  CL.asynchronouslyLoad,
  CL.asynchronouslyLoadElf,
  CL.asynchronouslyLoadJAR,
  CL.asynchronouslyLoadLLVM,
  -- ** Program representation
  CA.AnalysisResult,
  CA.ArchConstraints,
  CA.IR(..),
  IR.IRRepr(..),
  CA.SomeIRRepr(..),
  CA.Architecture(..),
  CA.SymbolicArchitecture(..),
  CA.Block(..),
  CA.BlockMapping(..),
  CA.FunctionHandle(..),
  CA.ParameterizedFormula(..),
  CA.prettyParameterizedFormula,
  CA.SomeResult(..),
  CA.CruciblePersonality,
  CA.LLVM,
  CA.mkLLVMResult,
  CA.LLVMPersonality(..),
  CA.llvmAnalysisResultFromModule,
  -- ** Operand lists
  OL.OperandList,
  OL.OperandListItem(..),
  OL.indexOperandList,
  OL.Delimiter(..),
  OL.Zipper,
  OL.zipper,
  OL.zipperNext,
  OL.zipperPrev,
  OL.zipperFocused,
  OL.listItems,
  -- * State
  module Surveyor.Core.State,
  CAS.asynchronously,
  SCV.ValueNameMap,
  SCV.emptyValueNameMap,
  SCV.addValueName,
  SCV.lookupValueName,
  -- ** Modes
  M.UIMode(..),
  M.UIKind,
  M.NormalK,
  M.MiniBufferK,
  M.SomeUIMode(..),
  M.prettyMode,
  -- * Completion system
  AR.SurveyorCommand,
  CC.Command(..),
  CC.SomeCommand(..),
  CC.ArgumentKind,
  CC.CommandLike(..),
  AR.Argument(..),
  AR.SomeAddress(..),
  AR.SomeState(..),
  -- ** Commands
  module Surveyor.Core.Commands,
  -- ** Types and type representatives for the completion system
  AR.HasNonce(..),
  AR.SomeNonce(..),
  AR.Type(..),
  AR.TypeRepr(..),
  AR.IntType,
  AR.WordType,
  AR.AddressType,
  AR.StringType,
  AR.CommandType,
  AR.FilePathType,
  AR.ValueNonceType,
  AR.showRepr,
  AR.parseArgument,
  -- * Context
  CCX.Context(..),
  CCX.InstructionSelection(..),
  CCX.ContextStack(..),
  CCX.BlockState(..),
  CCX.emptyContextStack,
  CCX.makeContext,
  CCX.selectedIndex,
  -- ** Symbolic Execution
  SymEx.Solver(..),
  SymEx.SymbolicExecutionConfig(..),
  SymEx.SessionID,
  SymEx.newSessionID,
  SymEx.sessionID,
  SymEx.SomeFloatModeRepr(..),
  SymEx.defaultSymbolicExecutionConfig,
  SymEx.SymbolicState(..),
  SymEx.symbolicSessionID,
  SymEx.SessionState,
  SymEx.lookupSessionState,
  SymEx.emptySessionState,
  SymEx.singleSessionState,
  SymEx.mergeSessionState,
  SymEx.updateSessionMetrics,
  SymEx.SymbolicExecutionState(..),
  SymEx.SuspendedState(..),
  SymEx.suspendedState,
  SymEx.Config,
  SymEx.SetupArgs,
  SymEx.Execute,
  SymEx.Inspect,
  SymEx.Suspend,
  SymEx.ExecutionProgress,
  SymEx.executionMetrics,
  SymEx.symbolicExecutionConfig,
  SymEx.configuringSymbolicExecution,
  SymEx.initializingSymbolicExecution,
  SymEx.startSymbolicExecution,
  SymEx.cleanupSymbolicExecutionState,
  SymEx.configSolverL,
  SymEx.configFloatReprL,
  SymEx.solverInteractionFileL,
  -- ** Breakpoints
  SB.Breakpoint(..),
  SB.BreakpointType(..),
  SB.classifyBreakpoint,
  -- ** Modifiers
  CCX.resetBlockSelection,
  CCX.selectNextInstruction,
  CCX.selectPreviousInstruction,
  CCX.selectNextOperand,
  CCX.selectPreviousOperand,
  CCX.selectNextBlock,
  CCX.selectPreviousBlock,
  CCX.pushContext,
  CCX.contextBack,
  CCX.contextForward,
  -- ** Lenses
  CCX.symExecSessionIDL,
  CCX.baseFunctionG,
  CCX.currentContext,
  CCX.blockStateFor,
  CCX.blockStateList,
  CCX.blockStateBlock,
  CCX.blockStateSelection,
  CCX.cfgG,
  CCX.vertexMapG,
  CCX.selectedBlockL,
  CCX.functionStateFor,
  -- * Translation Cache
  TC.TranslationCache,
  TC.newTranslationCache,
  -- * The EchoArea abstraction
  EA.EchoArea,
  EA.echoArea,
  EA.getEchoAreaText,
  EA.setEchoAreaText,
  EA.resetEchoArea,
  -- * Handlers
  HC.handleContextEvent,
  HI.handleInfoEvent,
  HL.handleLoggingEvent,
  -- * Keymap
  K.Keymap,
  K.Key(..),
  K.emptyKeymap,
  K.addGlobalKey,
  K.addModeKey,
  K.modeKeybindings,
  K.lookupKeyCommand,
  -- * Logging
  -- ** Log Actions
  SCL.LogAction,
  SCL.logToFile,
  SCL.logToState,
  SCL.defaultLogFile,
  -- ** Log Store
  SCL.LogStore,
  SCL.appendLog,
  SCL.takeLogs,
  -- ** Log Messages
  SCL.Source(..),
  SCL.Severity(..),
  SCL.LogMessage(..),
  SCL.msgWith,
  SCL.Timestamped,
  SCL.Timestamp,
  SCL.timestamp,
  SCL.logTime,
  SCL.logMsg
  ) where

import qualified Surveyor.Core.Architecture as CA
import qualified Surveyor.Core.Arguments as AR
import qualified Surveyor.Core.Async as CAS
import qualified Surveyor.Core.Breakpoint as SB
import qualified Surveyor.Core.Chan as CS
import qualified Surveyor.Core.Command as CC
import           Surveyor.Core.Commands
import qualified Surveyor.Core.Context as CCX
import qualified Surveyor.Core.EchoArea as EA
import qualified Surveyor.Core.Events as CE
import qualified Surveyor.Core.Handlers.Context as HC
import qualified Surveyor.Core.Handlers.Info as HI
import qualified Surveyor.Core.Handlers.Logging as HL
import qualified Surveyor.Core.IRRepr as IR
import qualified Surveyor.Core.Keymap as K
import qualified Surveyor.Core.Loader as CL
import qualified Surveyor.Core.Logging as SCL
import qualified Surveyor.Core.Mode as M
import qualified Surveyor.Core.OperandList as OL
import           Surveyor.Core.State
import qualified Surveyor.Core.SymbolicExecution as SymEx
import qualified Surveyor.Core.TranslationCache as TC
import qualified Surveyor.Core.ValueNames as SCV
