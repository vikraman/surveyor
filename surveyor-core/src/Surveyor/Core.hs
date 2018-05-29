module Surveyor.Core (
  -- * Channel abstraction
  CS.Chan,
  CS.mkChan,
  CS.readChan,
  CS.writeChan,
  -- * Events
  CE.Events(..),
  -- * Binaries
  -- ** Loading
  CL.AsyncLoader,
  CL.cancelLoader,
  CL.asynchronouslyLoad,
  CL.asynchronouslyLoadElf,
  CL.asynchronouslyLoadJAR,
  CL.asynchronouslyLoadLLVM,
  -- ** Program representation
  CA.Architecture(..),
  CA.Block(..),
  CA.FunctionHandle(..),
  CA.ParameterizedFormula(..),
  CA.prettyParameterizedFormula,
  CA.SomeResult(..),
  -- * State
  module Surveyor.Core.State,
  -- ** Modes
  M.UIMode(..),
  M.UIKind,
  M.NormalK,
  M.MiniBufferK,
  M.SomeUIMode(..),
  M.prettyMode,
  -- * Completion system
  CC.Command(..),
  AR.Argument(..),
  AR.SomeAddress(..),
  -- ** Commands
  module Surveyor.Core.Commands,
  -- ** Types and type representatives for the completion system
  AR.Type(..),
  AR.TypeRepr(..),
  AR.IntType,
  AR.WordType,
  AR.AddressType,
  AR.StringType,
  AR.CommandType,
  AR.FilePathType,
  AR.showRepr,
  AR.parseArgument,
  -- * The EchoArea abstraction
  EA.EchoArea,
  EA.echoArea,
  EA.getEchoAreaText,
  EA.setEchoAreaText,
  EA.resetEchoArea,
  -- * Keymap
  K.Keymap,
  K.Key(..),
  K.emptyKeymap,
  K.addGlobalKey,
  K.lookupKeyCommand,
  -- * Defaults
  defaultKeymap
  ) where

import qualified Data.Foldable as F
import           Data.Parameterized.Some ( Some(..) )
import qualified Graphics.Vty as V

import qualified Surveyor.Core.Architecture as CA
import qualified Surveyor.Core.Arguments as AR
import qualified Surveyor.Core.Chan as CS
import qualified Surveyor.Core.Command as CC
import           Surveyor.Core.Commands
import qualified Surveyor.Core.EchoArea as EA
import qualified Surveyor.Core.Events as CE
import qualified Surveyor.Core.Keymap as K
import qualified Surveyor.Core.Loader as CL
import qualified Surveyor.Core.Mode as M
import           Surveyor.Core.State

-- | A default keymap with some reasonable keybindings
defaultKeymap :: K.Keymap (CE.Events s) M.SomeUIMode (Maybe (SomeNonce s)) (AR.Argument (CE.Events s) (Maybe (SomeNonce s)) s) AR.TypeRepr
defaultKeymap = F.foldl' (\km (k, cmd) -> K.addGlobalKey k cmd km) K.emptyKeymap globals
  where
    globals = [ (K.Key (V.KChar 'q') [V.MCtrl], Some exitC)
              , (K.Key (V.KChar 'x') [V.MMeta], Some minibufferC)
              ]