{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
-- | This widget provides an interface for choosing the symbolic execution backend to use
--
-- The backend currently consists of a choice of SMT solver and floating point
-- interpretation.  These two parameters are a separate configuration step, as
-- changing them can invalidate the initial state setup (which is the next
-- configuration step after this one)
module Surveyor.Brick.Widget.SymbolicExecution.Configuration (
  form,
  renderSymbolicExecutionConfigurator,
  handleSymbolicExecutionConfiguratorEvent
  ) where

import           Brick ( (<+>) )
import qualified Brick as B
import           Brick.Forms ( (@@=) )
import qualified Brick.Forms as B
import qualified Data.Text as T
import qualified What4.Expr.Builder as WEB

import           Surveyor.Brick.Names ( Names(..) )
import qualified Surveyor.Core as C

form :: C.SymbolicExecutionConfig s -> B.Form (C.SymbolicExecutionConfig s) e Names
form = B.newForm [ (B.str "Solver: " <+>) @@= B.radioField C.configSolverL solvers
                 , (B.str "Floating point mode: " <+>) @@= B.radioField C.configFloatReprL floatModes
                 , (B.str "Solver interaction file: " <+>) @@= B.editTextField C.solverInteractionFileL SolverInteractionFileEdit Nothing
                 ]

solvers :: [(C.Solver, Names, T.Text)]
solvers = [ (C.CVC4, SolverRadioSelection C.CVC4, "CVC4")
          , (C.Yices, SolverRadioSelection C.Yices, "Yices")
          , (C.Z3, SolverRadioSelection C.Z3, "Z3")
          ]

floatModes :: [(C.SomeFloatModeRepr s, Names, T.Text)]
floatModes = [ (C.SomeFloatModeRepr WEB.FloatRealRepr, FloatModeRadioSelection "Real", "Real")
             , (C.SomeFloatModeRepr WEB.FloatIEEERepr, FloatModeRadioSelection "IEEE", "IEEE")
             , (C.SomeFloatModeRepr WEB.FloatUninterpretedRepr, FloatModeRadioSelection "Uninterpreted", "Uninterpreted")
             ]

renderSymbolicExecutionConfigurator :: B.Form (C.SymbolicExecutionConfig s) e Names
                                    -> B.Widget Names
renderSymbolicExecutionConfigurator = B.renderForm

handleSymbolicExecutionConfiguratorEvent :: B.BrickEvent Names e
                                         -> B.Form (C.SymbolicExecutionConfig s) e Names
                                         -> B.EventM Names (C.SymbolicExecutionState arch s C.Config, B.Form (C.SymbolicExecutionConfig s) e Names)
handleSymbolicExecutionConfiguratorEvent evt f = do
  f' <- B.handleFormEvent evt f
  return (C.Configuring (B.formState f'), f')
