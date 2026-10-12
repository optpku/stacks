/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap98.«98_8_0_2_DualNumber»

/-!
# Infinitesimal automorphisms in a category fibered in groupoids over `Over S`

Given a cartesian pullback `x₀'` of a residue object `x₀` to `Spec(k[ε])`, the group
`Inf(ℱ_{𝒳, k, x₀})` is the equalizer subgroup of fibre automorphisms of `x₀'` that
become the identity after precomposition with the unique cartesian section
`x₀ ⟶ x₀'`. This coincides with the kernel of restriction `Aut x₀' →* Aut x₀`
along that section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))
variable (x0' : X.p.Fiber (specDualNumber openImmersion k))
variable (φ : Fiber.fiberInclusion.obj x0' ⟶ Fiber.fiberInclusion.obj x0)
variable [X.p.IsHomLift (specDualNumberToResidue openImmersion k kToS h_factor) φ]
variable [X.p.IsStronglyCartesian (specDualNumberToResidue openImmersion k kToS h_factor) φ]

/-- The unique section of a cartesian dual-number pullback, obtained from the strongly
cartesian universal property applied to the identity on `x0`. -/
noncomputable def pullbackSection :
    Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj x0' :=
  IsStronglyCartesian.map X.p (specDualNumberToResidue openImmersion k kToS h_factor) φ
    (specDualNumberToResidue_comp openImmersion k kToS h_factor).symm
    (Fiber.fiberInclusion.map (𝟙 x0))

/-- The section of a dual-number pullback lies over `specOver_toResidue` of `dualNumber`. -/
instance pullbackSection_isHomLift :
    X.p.IsHomLift
      (specOver_toResidue openImmersion kToS h_factor (ArtinianLocalAlgCat.dualNumber Λ k))
      (pullbackSection openImmersion kToS h_factor X x0 x0' φ) :=
  IsStronglyCartesian.map_isHomLift X.p
    (specDualNumberToResidue openImmersion k kToS h_factor) φ
    (specDualNumberToResidue_comp openImmersion k kToS h_factor).symm
    (Fiber.fiberInclusion.map (𝟙 x0))

/-- The composite of the cartesian dual-number pullback with its section is the identity. -/
theorem pullbackSection_comp :
    pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫ φ =
      𝟙 (Fiber.fiberInclusion.obj x0) :=
  sorry

/-- The induced homomorphism `Aut x0' →* Aut x0` on the fibres over `Spec(k[ε])` and
`Spec(k)`, sending a fibre automorphism of `x0'` to the vertical automorphism of `x0`
obtained by conjugating with the cartesian section. -/
noncomputable def restrictAut : Aut x0' →* Aut x0 where
  toFun α :=
    Fiber.isoMk
      { hom := pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
          Fiber.fiberInclusion.map α.hom ≫ φ
        inv := pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
          Fiber.fiberInclusion.map α.inv ≫ φ
        hom_inv_id := sorry
        inv_hom_id := sorry }
      sorry
  map_one' := sorry
  map_mul' := sorry

/-- The induced fibre automorphism of `x0` is the conjugate of `α` by the cartesian section. -/
theorem restrictAut_apply (α : Aut x0') :
    Fiber.fiberInclusion.map (restrictAut openImmersion kToS h_factor X x0 x0' φ α).hom =
      pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
        Fiber.fiberInclusion.map α.hom ≫ φ :=
  sorry

/-- Restriction along the cartesian pullback is the conjugate of `α` by the cartesian section. -/
theorem restrictAut_comp (α : Aut x0') :
    pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫ Fiber.fiberInclusion.map α.hom ≫ φ =
      Fiber.fiberInclusion.map (restrictAut openImmersion kToS h_factor X x0 x0' φ α).hom :=
  sorry

/-- The group of infinitesimal automorphisms of `x0` along a cartesian pullback to
`Spec(k[ε])`. As a subgroup of `Aut x0'` it is the equalizer of precomposition
with the unique cartesian section. -/
noncomputable def infinitesimalAutomorphisms
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (x0 : X.p.Fiber (Over.mk kToS)) (x0' : X.p.Fiber (specDualNumber openImmersion k))
    (φ : Fiber.fiberInclusion.obj x0' ⟶ Fiber.fiberInclusion.obj x0)
    [X.p.IsHomLift (specDualNumberToResidue openImmersion k kToS h_factor) φ]
    [X.p.IsStronglyCartesian (specDualNumberToResidue openImmersion k kToS h_factor) φ] :
    Subgroup (Aut x0') where
  carrier :=
    {α | pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
          Fiber.fiberInclusion.map α.hom =
        pullbackSection openImmersion kToS h_factor X x0 x0' φ}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `infinitesimalAutomorphisms` is the equalizer condition that a fibre
automorphism of `x0'` becomes the identity after precomposition with the cartesian
section. -/
theorem mem_infinitesimalAutomorphisms (α : Aut x0') :
    α ∈ infinitesimalAutomorphisms openImmersion kToS h_factor X x0 x0' φ ↔
      pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
          Fiber.fiberInclusion.map α.hom =
        pullbackSection openImmersion kToS h_factor X x0 x0' φ :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
