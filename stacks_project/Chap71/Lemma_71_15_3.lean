module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple
public import stacks_project.Chap71.Lemma_71_15_2_Comparison
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap71.Lemma_71_15_3_Restrict

/-!
# Lemma 71.15.3

An invertible module that is ample on a scheme-theoretic fibre of a proper
morphism of algebraic spaces over a Noetherian scheme is relatively ample over
some open neighbourhood of that point.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.15.3: for a more general version see Descent on Spaces, Lemma 74.13.2.
Let `Y` be a Noetherian scheme. Let `X` be an algebraic space over `Y` whose
structure morphism `f : X ⟶ Y` is proper. Let `L` be an invertible `𝒪_X`-module.
Let `y ∈ Y` be a point such that the fibre `fiber f y` is a scheme, represented
by `e : fiber f y ≅ ofOver T`, and such that `moduleOnScheme f y e L` is ample
on that fibre. Then there exists an open neighbourhood `V ⊂ Y` of `y` such that
`Modules.restrictToBasePreimage f L V` is ample on `morphismRestrict f V` in the
sense of `RelativelyAmple`. -/
@[stacks 0D3A]
theorem RelativelyAmple.exists_morphismRestrict_of_isAmple_fiber
    {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
    (L : X.Modules) [isInvertibleObject L] (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T)
    [Scheme.Modules.IsAmple (moduleOnScheme f y e L)] :
    ∃ V : Y.Opens, y ∈ V ∧
      RelativelyAmple (morphismRestrict f V)
        (Modules.restrictToBasePreimage f L V) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
