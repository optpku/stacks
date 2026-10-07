module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Lemma_69_16_9
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Lemma 71.15.1

Relative ampleness of an invertible sheaf on a proper algebraic space over a
Noetherian ring is equivalent to eventual vanishing of positive-degree
cohomology of all coherent twists.
-/

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.15.1: let `R` be a Noetherian ring, let `X` be an algebraic space over
`R` whose structure morphism `f : X ⟶ Spec (CommRingCat.of R)` is proper, and let
`L` be an invertible `𝒪_X`-module. Then `L` is ample on `X/R` in the sense of
`RelativelyAmple f L` if and only if for every coherent `𝒪_X`-module `F` there
exists `n0 ≥ 0` such that `H^p(X, F ⊗ L^{⊗ n}) = 0` for all `n ≥ n0` and all
`p > 0`. -/
@[stacks 0D38]
theorem relativelyAmple_iff_twist_cohomology_eventually_isZero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔
      ∀ F : X.Modules, F.IsCoherent →
        ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ p, 0 < p →
          IsZero (cohomology X (F ⊗ Modules.tensorPowerInt L n) p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
