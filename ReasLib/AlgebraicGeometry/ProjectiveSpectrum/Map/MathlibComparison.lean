/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.TensorProductBaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.IdealClosure

/-!
# Comparison with mathlib's projective-spectrum maps

The natural-domain map is available for every graded ring homomorphism. Mathlib's `Proj.map`
requires the stronger containment of the target irrelevant ideal in the mapped source irrelevant
ideal. Under exactly that hypothesis the natural domain is the whole target, and the maps agree
by their homogeneous-localization formulas (Stacks, Tag 01MY).

Full natural domain alone does not imply this containment: with the induced grading,
`k[t²,t³] ⊆ k[t]` maps the irrelevant ideal to `(t²)`, whose radical is `(t)`.
The suppliers below apply to degreewise surjections, in particular homogeneous quotients,
and to arbitrary coefficient base change. They do not replace the natural-domain or twist owners.
-/

@[expose] public section

open CategoryTheory
open HomogeneousIdeal
open scoped TensorProduct

namespace AlgebraicGeometry

section GradedRing

universe u

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : ℕ → sigma} {calB : ℕ → tau} [GradedRing calA] [GradedRing calB]

/-- Mathlib's irrelevant-ideal containment makes the natural domain the full target. -/
theorem projMapDomain_eq_top_of_mathlibMap_hyp
    (psi : calA →+*ᵍ calB)
    (hf : irrelevant calB ≤ (irrelevant calA).map psi) :
    projMapDomain psi = ⊤ := by
  apply top_unique
  intro point _
  by_contra hpoint
  have hcomap : irrelevant calA ≤ point.asHomogeneousIdeal.comap psi := by
    apply (irrelevant_le calA).mpr
    intro degree hdegree element helement
    change psi element ∈ point.asHomogeneousIdeal
    by_contra hmem
    exact hpoint (TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨element, degree, hdegree, helement⟩, hmem⟩)
  exact point.not_irrelevant_le (hf.trans (map_le_of_le_comap psi hcomap))

/-- Restricting mathlib's map to the natural domain gives the glued map. -/
theorem projMapDomain_ι_comp_mathlibMap
    (psi : calA →+*ᵍ calB)
    (hf : irrelevant calB ≤ (irrelevant calA).map psi) :
    (projMapDomain psi).ι ≫ Proj.map psi hf = projMapMap psi := by
  apply projMapMap_unique
  intro element degree hdegree helement
  simpa only [← Category.assoc, Scheme.homOfLE_ι, Proj.awayι] using
    (Proj.awayι_comp_map psi hf hdegree element helement)

/-- The existing full-domain wrapper agrees with mathlib's map; `hf` is still required. -/
theorem projMapOnTarget_eq_mathlibMap
    (psi : calA →+*ᵍ calB)
    (hf : irrelevant calB ≤ (irrelevant calA).map psi)
    (hU : projMapDomain psi = ⊤) :
    projMapOnTarget psi (projMapMap psi) hU = Proj.map psi hf := by
  rw [projMapOnTarget, ← projMapDomain_ι_comp_mathlibMap psi hf]
  simp [projMapDomainTopInclusion, Category.assoc]

/-- A twist-compatible map retains its comparison data while its scheme map agrees with
the restriction of mathlib's map. -/
theorem ProjMap.map_eq_restrict_mathlibMap
    {PcalA : ProjTwistPresentation calA} {PcalB : ProjTwistPresentation calB}
    {psi : calA →+*ᵍ calB} (hProj : ProjMap PcalA PcalB psi)
    (hf : irrelevant calB ≤ (irrelevant calA).map psi) :
    hProj.map = (projMapDomain psi).ι ≫ Proj.map psi hf := by
  rw [projMapDomain_ι_comp_mathlibMap psi hf]
  exact projMapMap_unique psi hProj.map hProj.basicOpenIsoSpec_inv_comp

/-- Surjectivity in every positive degree supplies mathlib's stronger hypothesis.
Eventual surjectivity alone is deliberately not used here. -/
theorem projMap_irrelevant_le_map_of_degreewise_surjective
    (psi : calA →+*ᵍ calB)
    (hsurj : ∀ degree : ℕ, 0 < degree → Function.Surjective (psi.gradedAddHom degree)) :
    irrelevant calB ≤ (irrelevant calA).map psi := by
  apply (irrelevant_le calB).mpr
  intro degree hdegree element helement
  obtain ⟨preimage, hpreimage⟩ := hsurj degree hdegree ⟨element, helement⟩
  have heq : psi preimage.val = element := congrArg Subtype.val hpreimage
  change element ∈ (irrelevant calA).toIdeal.map psi.toRingHom
  rw [← heq]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem calA hdegree preimage.property)

end GradedRing

section Quotient

universe u v

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (calA : ℕ → Submodule R A) [GradedAlgebra calA]

/-- The canonical homogeneous quotient map satisfies mathlib's irrelevant-ideal containment. -/
theorem projQuotientGradedHom_irrelevant_le_map (I : HomogeneousIdeal calA) :
    letI := GradedAlgebra.Quotient.gradedAlgebra calA I.toIdeal I.isHomogeneous
    irrelevant (GradedAlgebra.Quotient.grading calA I.toIdeal) ≤
      (irrelevant calA).map (projQuotientGradedHom calA I) := by
  letI := GradedAlgebra.Quotient.gradedAlgebra calA I.toIdeal I.isHomogeneous
  apply projMap_irrelevant_le_map_of_degreewise_surjective
  intro degree _
  exact GradedAlgebra.Quotient.componentMap_surjective calA I.toIdeal degree

/-- The existing homogeneous quotient morphism is mathlib's morphism for the same graded map. -/
theorem projQuotientMap_eq_mathlibMap (I : HomogeneousIdeal calA) :
    letI := GradedAlgebra.Quotient.gradedAlgebra calA I.toIdeal I.isHomogeneous
    projQuotientMap calA I =
      Proj.map (projQuotientGradedHom calA I)
        (projQuotientGradedHom_irrelevant_le_map calA I) := by
  letI := GradedAlgebra.Quotient.gradedAlgebra calA I.toIdeal I.isHomogeneous
  exact projMapOnTarget_eq_mathlibMap (projQuotientGradedHom calA I)
    (projQuotientGradedHom_irrelevant_le_map calA I) _

end Quotient

section TensorProduct

universe u

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
  [Algebra R R'] [Algebra R A]
  (calA : ℕ → Submodule R A) [GradedAlgebra calA]

/-- Coefficient base change satisfies mathlib's containment, without a flatness assumption. -/
theorem tensorProductBaseChangePsi_irrelevant_le_map :
    irrelevant (tensorProductBaseChangeGrading (R' := R') calA) ≤
      (irrelevant calA).map (tensorProductBaseChangePsi calA) := by
  apply (irrelevant_le _).mpr
  intro degree hdegree element helement
  change element ∈ (irrelevant calA).toIdeal.map (tensorProductBaseChangePsi calA).toRingHom
  change element ∈ (calA degree).baseChange R' at helement
  rw [Submodule.baseChange_eq_span] at helement
  induction helement using Submodule.span_induction with
  | mem element helement =>
      obtain ⟨preimage, hpreimage, rfl⟩ := helement
      exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem calA hdegree hpreimage)
  | zero => exact Ideal.zero_mem _
  | add first second _ _ hfirst hsecond => exact Ideal.add_mem _ hfirst hsecond
  | smul scalar element _ ih =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ ih

/-- The tensor-product base-change map, extended by the proved containment, agrees with mathlib. -/
theorem tensorProductBaseChange_projMapOnTarget_eq_mathlibMap :
    projMapOnTarget (tensorProductBaseChangePsi (R' := R') calA)
        (projMapMap (tensorProductBaseChangePsi calA))
        (projMapDomain_eq_top_of_mathlibMap_hyp _
          (tensorProductBaseChangePsi_irrelevant_le_map calA)) =
      Proj.map (tensorProductBaseChangePsi calA)
        (tensorProductBaseChangePsi_irrelevant_le_map calA) :=
  projMapOnTarget_eq_mathlibMap _ (tensorProductBaseChangePsi_irrelevant_le_map calA) _

end TensorProduct

end AlgebraicGeometry
