/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

@[expose] public section

noncomputable section

universe u

/-- The ambient tensor product preserves quasicoherence, so it can be restricted
to the full subcategory `Scheme.QCoh`. -/
theorem tensorRightPreservesQuasiCoherent {P : Scheme.{u}} (K : Scheme.QCoh P) :
    Scheme.quasiCoherentModuleProperty P ≤
      (Scheme.quasiCoherentModuleProperty P).inverseImage
        (tensorRight K.obj) := sorry

/-- The tensor-by-kernel functor on quasicoherent modules. -/
noncomputable def quasiCoherentTensorRight {P : Scheme.{u}} (K : Scheme.QCoh P) :
    Scheme.QCoh P ⥤ Scheme.QCoh P :=
  ObjectProperty.FullSubcategory.restrict
    (tensorRight K.obj) (tensorRightPreservesQuasiCoherent K)

/-- 56.5.1.1: For schemes `X` and `Y` over `R`, with kernel `K` on
`Limits.pullback x y`, the Fourier--Mukai functor is the composition of
`Scheme.QCoh.pullback (Limits.pullback.fst x y)`, tensoring by `K`, and
`Scheme.QCoh.pushforward (Limits.pullback.snd x y)`. -/
@[stacks 0FZC]
noncomputable def fourierMukaiFunctor
    {R X Y : Scheme.{u}} (x : X ⟶ R) (y : Y ⟶ R)
    [QuasiCompact (Limits.pullback.snd x y)]
    [QuasiSeparated (Limits.pullback.snd x y)]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    Scheme.QCoh X ⥤ Scheme.QCoh Y :=
  Scheme.QCoh.pullback (Limits.pullback.fst x y) ⋙
    quasiCoherentTensorRight K ⋙
      Scheme.QCoh.pushforward (Limits.pullback.snd x y)

/-- The object map of `fourierMukaiFunctor` is the pullback--tensor--pushforward
construction displayed in the defining equation. -/
theorem fourierMukaiFunctor_obj
    {R X Y : Scheme.{u}} (x : X ⟶ R) (y : Y ⟶ R)
    [QuasiCompact (Limits.pullback.snd x y)]
    [QuasiSeparated (Limits.pullback.snd x y)]
    (K : Scheme.QCoh (Limits.pullback x y)) (F : Scheme.QCoh X) :
    (fourierMukaiFunctor x y K).obj F =
      (Scheme.QCoh.pushforward (Limits.pullback.snd x y)).obj
        ((quasiCoherentTensorRight K).obj
          ((Scheme.QCoh.pullback (Limits.pullback.fst x y)).obj F)) := sorry


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
