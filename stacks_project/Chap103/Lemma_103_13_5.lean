/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.FinitePresentation.FilteredColimit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FppfSite.QuasiCompact
import StacksCheckRecall

/-!
# Lemma 103.13.5

Hom out of a finitely presented module on a qcqs algebraic stack commutes with
filtered colimits of `𝒪_X`-modules, and in particular with filtered colimits in
`QCoh(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 103.13.5 (1): let `X` be a quasi-compact and quasi-separated algebraic
stack. Let `G` be a finitely presented `𝒪_X`-module. Then `Hom_X(G, -)`
commutes with filtered colimits of arbitrary `𝒪_X`-modules. -/
@[stacks 0GQZ]
#check
  (AlgebraicGeometry.AlgebraicStack.homComparison_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
      (G : SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
      [G.IsFinitePresentation]
      (F : Λ ⥤ SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
      [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))],
      IsIso (colimit.post F (coyoneda.obj (op G))))

#check
  (AlgebraicGeometry.AlgebraicStack.isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      (G : SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
      [G.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)

/- Lemma 103.13.5 (2): in particular, `Hom_X(G, -)` commutes with filtered
colimits in `QCoh(𝒪_X)`. -/
@[stacks 0GQZ]
#check
  (AlgebraicGeometry.GroupoidsOver.QCoh.isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      (G : QCoh X) [G.obj.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)
