/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import ReasLib.RingTheory.GradedAlgebra.PositiveGenerators
public import ReasLib.RingTheory.GradedAlgebra.Quotient
public import ReasLib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Ideal closure on projective spectra

This module constructs the homogeneous ideal recovered from the closed projective subscheme
defined by a homogeneous ideal.  The construction uses the quotient projective-spectrum map and
global sections of pullbacks of the ambient associated shifts.
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry

section Closure

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The quotient homomorphism of a graded algebra by a homogeneous ideal. -/
noncomputable def projQuotientGradedHom (I : HomogeneousIdeal 𝒜) :
    𝒜 →+*ᵍ GradedAlgebra.Quotient.grading 𝒜 I.toIdeal where
  toRingHom := (Ideal.Quotient.mkₐ R I.toIdeal).toRingHom
  map_mem := fun ha ↦ GradedAlgebra.Quotient.mk_mem_grading 𝒜 I.toIdeal ha

/-- The morphism from the projective spectrum of a homogeneous quotient to the ambient
projective spectrum. -/
noncomputable def projQuotientMap (I : HomogeneousIdeal 𝒜) :
    -- Local instance justification (defeq pin): the result type must use the canonical
    -- homogeneous-quotient grading for definitional equality with the constructed Proj map.
    letI := GradedAlgebra.Quotient.gradedAlgebra 𝒜 I.toIdeal I.isHomogeneous
    Proj (GradedAlgebra.Quotient.grading 𝒜 I.toIdeal) ⟶ Proj 𝒜 :=
  -- Local instance justification (defeq pin): the quotient grading has this canonical
  -- decomposition, and the resulting projective spectrum must use that exact structure.
  letI := GradedAlgebra.Quotient.gradedAlgebra 𝒜 I.toIdeal I.isHomogeneous
  let ψ := projQuotientGradedHom 𝒜 I
  let hsurj : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → Function.Surjective (ψ.gradedAddHom d) :=
    ⟨0, fun d _ ↦ GradedAlgebra.Quotient.componentMap_surjective 𝒜 I.toIdeal d⟩
  projMapOnTarget ψ (projMapMap ψ)
    (projMapDomain_eq_top_of_eventually_surjective hsurj)

/-- The projective-spectrum morphism induced by a homogeneous quotient is a closed immersion. -/
theorem projQuotientMap_isClosedImmersion (I : HomogeneousIdeal 𝒜) :
    -- Local instance justification (defeq pin): the theorem must use the same canonical
    -- homogeneous-quotient grading as `projQuotientMap` for definitional equality.
    letI := GradedAlgebra.Quotient.gradedAlgebra 𝒜 I.toIdeal I.isHomogeneous
    IsClosedImmersion (projQuotientMap 𝒜 I) := sorry

/-- The degree-`n` global sections on `Proj(A/I)` of the pullback of the ambient associated
shift on `Proj(A)`. -/
abbrev projClosedSubschemeSections (I : HomogeneousIdeal 𝒜) (n : ℕ) : Type v :=
  -- Local instance justification (defeq pin): the quotient projective spectrum uses the
  -- canonical decomposition attached to the homogeneous quotient.
  letI := GradedAlgebra.Quotient.gradedAlgebra 𝒜 I.toIdeal I.isHomogeneous
  let hself : SetLike.GradedSMul 𝒜 𝒜 :=
    @SetLike.GradedMul.toGradedSMul ℕ A _ _
      (Submodule R A) _ 𝒜 GradedRing.toGradedMonoid
  let hnat : SetLike.GradedSMul 𝒜
      (DirectSum.Decomposition.natToIntGrading 𝒜) :=
    @DirectSum.Decomposition.natToIntGrading_gradedSMul R _ A _ _
      A (Submodule R A) _ _ 𝒜 𝒜 hself
  let hshift : SetLike.GradedSMul 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ)) :=
    @GradedModule.instShiftGradingGradedSMul R A A _ _ _ _ _ _
      𝒜 (DirectSum.Decomposition.natToIntGrading 𝒜) hnat (n : ℤ)
  Γ((Scheme.Modules.pullback (projQuotientMap 𝒜 I)).obj
    (@Proj.AssociatedModule.sheaf R A A _ _ _ _ _ _
      (Submodule R A) _ _ 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ)) hshift _), ⊤)

/-- The canonical map from an ambient homogeneous component to the corresponding restricted
ambient-twist sections on the quotient projective spectrum. -/
noncomputable def projClosedSubschemeDegreeMap (I : HomogeneousIdeal 𝒜) (n : ℕ) :
    𝒜 n →+ projClosedSubschemeSections 𝒜 I n :=
  -- Local instance justification (defeq pin): the quotient projective spectrum uses the
  -- canonical decomposition attached to the homogeneous quotient.
  letI := GradedAlgebra.Quotient.gradedAlgebra 𝒜 I.toIdeal I.isHomogeneous
  let hself : SetLike.GradedSMul 𝒜 𝒜 :=
    @SetLike.GradedMul.toGradedSMul ℕ A _ _
      (Submodule R A) _ 𝒜 GradedRing.toGradedMonoid
  let hnat : SetLike.GradedSMul 𝒜
      (DirectSum.Decomposition.natToIntGrading 𝒜) :=
    @DirectSum.Decomposition.natToIntGrading_gradedSMul R _ A _ _
      A (Submodule R A) _ _ 𝒜 𝒜 hself
  let hshift : SetLike.GradedSMul 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ)) :=
    @GradedModule.instShiftGradingGradedSMul R A A _ _ _ _ _ _
      𝒜 (DirectSum.Decomposition.natToIntGrading 𝒜) hnat (n : ℤ)
  let shiftEquiv : 𝒜 n ≃ₗ[R]
      GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ) 0 :=
    LinearEquiv.ofEq _ _ (by simp)
  let ambientShift :=
    @Proj.AssociatedModule.sheaf R A A _ _ _ _ _ _
      (Submodule R A) _ _ 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ)) hshift _
  let sectionMap :=
    @Proj.AssociatedModule.degreeZeroToGlobalSections R A A _ _ _ _ _ _
      (Submodule R A) _ _ 𝒜
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) (n : ℤ)) hshift _
  (Scheme.Modules.globalSectionsPullback (projQuotientMap 𝒜 I) ambientShift).hom.comp <|
    sectionMap.toAddMonoidHom.comp shiftEquiv.toLinearMap.toAddMonoidHom

/-- The canonical additive map from a graded algebra to the direct sum of restricted
ambient-twist sections on the projective spectrum of a homogeneous quotient. -/
noncomputable def projClosedSubschemeSectionMap (I : HomogeneousIdeal 𝒜) :
    A →+ DirectSum ℕ (projClosedSubschemeSections 𝒜 I) :=
  (DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (projClosedSubschemeSections 𝒜 I) n).comp
      (projClosedSubschemeDegreeMap 𝒜 I n)).comp
        (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

/-- A homogeneous element is sent to the matching summand of the restricted-twist section
direct sum. -/
theorem projClosedSubschemeSectionMap_of (I : HomogeneousIdeal 𝒜) (n : ℕ) (a : 𝒜 n) :
    projClosedSubschemeSectionMap 𝒜 I (a : A) =
      DirectSum.of (projClosedSubschemeSections 𝒜 I) n
        (projClosedSubschemeDegreeMap 𝒜 I n a) := sorry

/-- The homogeneous ideal recovered from the kernel of the canonical restricted-twist section
map. -/
noncomputable def projClosedSubschemeIdeal (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal 𝒜 :=
  (Ideal.span ((projClosedSubschemeSectionMap 𝒜 I).ker : Set A)).homogeneousCore 𝒜

/-- Membership in the ideal recovered from a projective closed subscheme is vanishing under the
canonical restricted-twist section map. -/
theorem mem_projClosedSubschemeIdeal_iff (I : HomogeneousIdeal 𝒜) (x : A) :
    x ∈ projClosedSubschemeIdeal 𝒜 I ↔ projClosedSubschemeSectionMap 𝒜 I x = 0 := sorry

/-- The saturation of a homogeneous ideal by powers of the irrelevant ideal. -/
noncomputable def projSaturation (I : HomogeneousIdeal 𝒜) : Ideal A :=
  ⨆ n : ℕ, I.toIdeal.colon
    (((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ n : Ideal A) : Set A)

/-- An element belongs to the irrelevant-ideal saturation exactly when one power of the
irrelevant ideal sends it into the original ideal. -/
theorem mem_projSaturation_iff (I : HomogeneousIdeal 𝒜) (x : A) :
    x ∈ projSaturation 𝒜 I ↔
      ∃ n : ℕ, ∀ a ∈ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ n : Ideal A),
        a * x ∈ I := sorry

/-- The degree-component saturation set `{x | 𝒜 n * x ⊆ I for some n}`. -/
def projDegreeOneSaturationSet (I : Ideal A) : Set A :=
  {x | ∃ n : ℕ, ∀ a : A, a ∈ 𝒜 n → a * x ∈ I}

/-- The degree-multiple closure, tested on each homogeneous component of an element.
For the degree-`i` component `xᵢ`, every product `b * xᵢ` of degree `n * d` must lie in
`I` for all sufficiently large `n`. On a homogeneous element this is the source condition
`(A * x)_(n*d) ⊆ I`; applying it componentwise also includes nonhomogeneous elements in
the graded closure. -/
def projDegreeMultipleClosureSet (I : Ideal A) (d : ℕ) : Set A :=
  {x | ∀ i : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ j : ℕ, j + i = n * d →
    ∀ b : A, b ∈ 𝒜 j → b * GradedRing.proj 𝒜 i x ∈ I}

/-- On a homogeneous element, degree-multiple closure is exactly eventual containment of
the degree-`n * d` part of its principal ideal. -/
theorem mem_projDegreeMultipleClosureSet_iff_of_mem (I : Ideal A) (d i : ℕ)
    {x : A} (hx : x ∈ 𝒜 i) :
    x ∈ projDegreeMultipleClosureSet 𝒜 I d ↔
      ∀ᶠ n : ℕ in Filter.atTop, ∀ a : A,
        a ∈ 𝒜 (n * d) → a ∈ Ideal.span ({x} : Set A) → a ∈ I := sorry

/-- For an algebra generated in degree one, irrelevant-ideal saturation is the same as
degree-component saturation. -/
theorem projSaturation_eq_degreeOneSaturationSet [IsNoetherianRing A]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) (I : HomogeneousIdeal 𝒜) :
    (projSaturation 𝒜 I : Set A) = projDegreeOneSaturationSet 𝒜 I.toIdeal := sorry

/-- For a Noetherian algebra generated in degree one, the ideal recovered from the associated
projective closed subscheme is its degree-component saturation. -/
theorem projClosedSubschemeIdeal_eq_degreeOneSaturation [IsNoetherianRing A]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) (I : HomogeneousIdeal 𝒜) :
    (projClosedSubschemeIdeal 𝒜 I : Set A) =
      projDegreeOneSaturationSet 𝒜 I.toIdeal := sorry

/-- In a Noetherian algebra generated in degree one, the ideals fixed by projective closure are
exactly the ideals equal to their irrelevant-ideal saturation. -/
theorem projClosedSubschemeIdeal_eq_self_iff_saturated [IsNoetherianRing A]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) (I : HomogeneousIdeal 𝒜) :
    projClosedSubschemeIdeal 𝒜 I = I ↔ I.toIdeal = projSaturation 𝒜 I := sorry

end Closure

section IntegerGrading

variable {A : Type v} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- For a finitely generated Noetherian graded ring, projective closure is detected in all
sufficiently large degrees divisible by the period of chosen positive homogeneous generators. -/
theorem projClosedSubschemeIdeal_eq_degreeMultipleClosure [IsNoetherianRing A]
    (G : GradedAlgebra.PositiveGenerators 𝒜) (I : HomogeneousIdeal 𝒜) :
    (projClosedSubschemeIdeal 𝒜 I : Set A) =
      projDegreeMultipleClosureSet 𝒜 I.toIdeal G.period := sorry

end IntegerGrading

end AlgebraicGeometry
