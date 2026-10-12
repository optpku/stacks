/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap76.Lemma_76_7_6_Comparison
public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified

/-!
# Pullback of differentials along a universal first-order thickening

For a formally unramified morphism `h : Z ⟶ X` of algebraic spaces over `B`,
the Lemma 76.7.6 comparison of the universal first-order thickening
`i : Z ⟶ Z'` over `X` becomes an isomorphism after pullback along `i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable (w : i ≫ h' = h)

/-- The canonical map `h^* Ω_{X/B} ⟶ i^* Ω_{Z'/B}` obtained by pulling the
differentials comparison `dh' : (h')^* Ω_{X/B} ⟶ Ω_{Z'/B}` back along the
universal first-order thickening `i : Z ⟶ Z'`, after identifying `h^*` with
`i^* ∘ (h')^*`. Source notation `Ω_{Z'/B} ⊗ 𝒪_Z` is this module pullback. -/
noncomputable def pullbackDifferentialsComparison :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      (Modules.pullback i).obj (relativeDifferentials (h' ≫ f)) :=
  (eqToIso (congrArg Modules.pullback w)).inv.app (relativeDifferentials f) ≫
    (Modules.pullbackComp i h').inv.app (relativeDifferentials f) ≫
      (Modules.pullback i).map
        (Hom.Differentials.comparison h' (𝟙 B) f (h' ≫ f)
          (Eq.symm (Category.comp_id (h' ≫ f))))

/-- `pullbackDifferentialsComparison` is the composite of `eqToIso` of
`i ≫ h' = h`, the inverse of `Modules.pullbackComp i h'`, and `i^*` of the
differentials comparison on the identity square of `B`. -/
theorem pullbackDifferentialsComparison_spec :
    pullbackDifferentialsComparison i h' h f w =
      (eqToIso (congrArg Modules.pullback w)).inv.app (relativeDifferentials f) ≫
        (Modules.pullbackComp i h').inv.app (relativeDifferentials f) ≫
          (Modules.pullback i).map
            (Hom.Differentials.comparison h' (𝟙 B) f (h' ≫ f)
              (Eq.symm (Category.comp_id (h' ≫ f)))) :=
  sorry

/-- Pulling the canonical relative-differentials comparison of a universal
first-order thickening of a formally unramified morphism back to `Z` is an
isomorphism. -/
instance pullbackDifferentialsComparison_isIso :
    IsIso (pullbackDifferentialsComparison i h' h f w) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
