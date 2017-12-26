{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
module Surveyor.Commands (
  exitC,
  showSummaryC,
  showDiagnosticsC,
  findBlockC,
  describeCommandC,
  minibufferC,
  allCommands
  ) where

import qualified Brick.BChan as B
import qualified Data.Functor.Const as C
import qualified Data.Parameterized.List as PL
import           Data.Parameterized.Some ( Some(..) )

import qualified Brick.Command as C
import qualified Surveyor.Minibuffer as MB
import           Surveyor.Events ( Events(..) )

allCommands :: B.BChan (Events s) -> [Some (C.Command MB.Argument MB.TypeRepr)]
allCommands customEventChan =
  [ Some (showSummaryC customEventChan)
  , Some (exitC customEventChan)
  , Some (showDiagnosticsC customEventChan)
  , Some (findBlockC customEventChan)
  , Some (describeCommandC customEventChan)
  ]

exitC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[]
exitC customEventChan =
  C.Command "exit" doc PL.Nil PL.Nil callback
  where
    doc = "Exit the application"
    callback = \PL.Nil -> B.writeBChan customEventChan Exit

showSummaryC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[]
showSummaryC customEventChan =
  C.Command "summary" doc PL.Nil PL.Nil callback
  where
    doc = "Show a summary of the information discovered about the binary"
    callback = \PL.Nil -> B.writeBChan customEventChan ShowSummary

showDiagnosticsC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[]
showDiagnosticsC customEventChan =
  C.Command "log" doc PL.Nil PL.Nil callback
  where
    doc = "Show a log of the diagnostics produced by the analysis and UI"
    callback = \PL.Nil -> B.writeBChan customEventChan ShowDiagnostics

findBlockC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[MB.AddressType]
findBlockC customEventChan =
  C.Command "find-block" doc names rep callback
  where
    doc = "Find the block(s) containing the given address and list them"
    names = C.Const "address" PL.:< PL.Nil
    rep = MB.AddressTypeRepr PL.:< PL.Nil
    callback = \(MB.AddressArgument addr PL.:< PL.Nil) ->
      B.writeBChan customEventChan (FindBlockContaining addr)

describeCommandC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[MB.CommandType]
describeCommandC customEventChan =
  C.Command "describe-command" doc names rep callback
  where
    doc = "Display the docstring of the named command"
    names = C.Const "command-name" PL.:< PL.Nil
    rep = MB.CommandTypeRepr PL.:< PL.Nil
    callback = \(MB.CommandArgument cmd PL.:< PL.Nil) ->
      B.writeBChan customEventChan (DescribeCommand cmd)

-- | This isn't part of 'allCommands' because we can never productively launch
-- it from the minibuffer
minibufferC :: B.BChan (Events s) -> C.Command MB.Argument MB.TypeRepr '[]
minibufferC customEventChan =
  C.Command "show-minibuffer" doc PL.Nil PL.Nil callback
  where
    doc = "Open the minibuffer"
    callback = \PL.Nil -> B.writeBChan customEventChan OpenMinibuffer