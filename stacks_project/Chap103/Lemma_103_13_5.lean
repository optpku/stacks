/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_13_5_Hom
public import stacks_project.Chap103.Lemma_103_13_5_TestSet
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
  (homComparison_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
      (G : RingedSite.ModuleCat.{u} (fppfRingedSite X)) [G.IsFinitePresentation]
      (F : Λ ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))
      [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))],
      IsIso (homComparison G F))

@[stacks 0GQZ]
#check
  (isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      (G : RingedSite.ModuleCat.{u} (fppfRingedSite X)) [G.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)

/- Lemma 103.13.5 (2): in particular, `Hom_X(G, -)` commutes with filtered
colimits in `QCoh(𝒪_X)`. -/
@[stacks 0GQZ]
#check
  (QCoh.isFinitelyPresentable :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
      (G : QCoh X) [G.obj.IsFinitePresentation],
      IsFinitelyPresentable.{u + 1} G)
