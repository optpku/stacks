/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap81.Lemma_81_10_2_Comparison

/-!
# Lemma 81.10.2

For a morphism of algebraic spaces whose inverse image of a closed subspace is
integral and universally injective, the canonical map of two-term complexes of
abelian étale stalks comparing pushforward at the image geometric point with
the source stalks is an isomorphism on kernels and a monomorphism on cokernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.10.2 (1): Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. Let `i : Z ⟶ X` be a closed immersion such that `inverseImageTo f i`
is integral and universally injective. Let `ybar` be a geometric point of `Y` and let
`G` be an abelian étale sheaf on `Y`. Write `V = closedImmersionComplement (inverseImageι f i)`
and `j' = complementOpenImmersion f i`. The canonical map of two-term complexes
`(f_* G)_{ybar.map f} ⟶ (f_* j'_*(j'⁻¹ G))_{ybar.map f}` to
`G_ybar ⟶ (j'_*(j'⁻¹ G))_ybar` induces an isomorphism on kernels. -/
@[stacks 0AER]
theorem twoTermStalkComparison_kernel_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegralHom (inverseImageTo f i)] [UniversallyInjective (inverseImageTo f i)]
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    IsIso ((ker AddCommGrpCat.{u + 1}).map (twoTermStalkComparison f i ybar G)) :=
  sorry

/-- Lemma 81.10.2 (2): Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. Let `i : Z ⟶ X` be a closed immersion such that `inverseImageTo f i`
is integral and universally injective. Let `ybar` be a geometric point of `Y` and let
`G` be an abelian étale sheaf on `Y`. Write `V = closedImmersionComplement (inverseImageι f i)`
and `j' = complementOpenImmersion f i`. The canonical map of two-term complexes
`(f_* G)_{ybar.map f} ⟶ (f_* j'_*(j'⁻¹ G))_{ybar.map f}` to
`G_ybar ⟶ (j'_*(j'⁻¹ G))_ybar` induces a monomorphism on cokernels. -/
@[stacks 0AER]
theorem twoTermStalkComparison_cokernel_mono {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegralHom (inverseImageTo f i)] [UniversallyInjective (inverseImageTo f i)]
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    Mono ((coker AddCommGrpCat.{u + 1}).map (twoTermStalkComparison f i ybar G)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
