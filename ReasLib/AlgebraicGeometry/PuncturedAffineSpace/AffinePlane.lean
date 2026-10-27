/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.FinCases

/-!
# The punctured affine plane
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

universe u

namespace PuncturedAffinePlane

section CommRing

variable (k : Type u) [CommRing k]

/-- The coordinate ring `k[x,y]` of the affine plane. -/
@[stacks 01IL "punctured affine-plane coordinate ring"]
abbrev coordinateRing : Type u :=
  PuncturedAffineSpace.coordinateRing (ULift.{u} (Fin 2)) k

/-- The affine plane over `k`, using mathlib's relative affine-space owner. -/
@[stacks 01IL "punctured affine-plane affine-space model"]
abbrev affinePlane : Scheme.{u} :=
  PuncturedAffineSpace.affineSpace (ULift.{u} (Fin 2)) k

/-- The canonical structure morphism from affine `2`-space to `Spec(k)`. -/
@[stacks 01IL "punctured affine-plane structure morphism"]
abbrev toBase : affinePlane k ⟶ Spec (CommRingCat.of k) :=
  PuncturedAffineSpace.toBase (ULift.{u} (Fin 2)) k

/-- The polynomial coordinate `x`. -/
@[stacks 01IL "punctured affine-plane x coordinate"]
abbrev x : coordinateRing k :=
  PuncturedAffineSpace.coordinate (ULift.{u} (Fin 2)) k (ULift.up 0)

/-- The polynomial coordinate `y`. -/
@[stacks 01IL "punctured affine-plane y coordinate"]
abbrev y : coordinateRing k :=
  PuncturedAffineSpace.coordinate (ULift.{u} (Fin 2)) k (ULift.up 1)

/-- The global coordinate section `x`. -/
@[stacks 01IL "punctured affine-plane x section"]
abbrev xSection : Γ(affinePlane k, ⊤) :=
  PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up 0)

/-- The global coordinate section `y`. -/
@[stacks 01IL "punctured affine-plane y section"]
abbrev ySection : Γ(affinePlane k, ⊤) :=
  PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up 1)

/-- Evaluation at the affine-plane origin as a `k`-algebra homomorphism. -/
@[stacks 01IL "punctured affine-plane origin algebra map"]
abbrev evalAtOriginAlgHom : coordinateRing k →ₐ[k] k :=
  PuncturedAffineSpace.evalAtOriginAlgHom (ULift.{u} (Fin 2)) k

/-- The ring-hom view of evaluation at the affine-plane origin. -/
@[stacks 01IL "punctured affine-plane origin evaluation"]
abbrev evalAtOrigin : coordinateRing k →+* k :=
  (evalAtOriginAlgHom k).toRingHom

/-- The ideal of functions vanishing along the zero section. -/
@[stacks 01IL "punctured affine-plane origin ideal"]
abbrev originIdeal : Ideal (coordinateRing k) :=
  PuncturedAffineSpace.originIdeal (ULift.{u} (Fin 2)) k

/-- The kernel description of the origin is the ideal `(x,y)`. -/
@[stacks 01IL "punctured affine-plane origin ideal generators"]
theorem originIdeal_eq_span :
    originIdeal k = Ideal.span ({x k, y k} : Set (coordinateRing k)) := by
  let I := Ideal.span ({x k, y k} : Set (coordinateRing k))
  have hX (i : ULift.{u} (Fin 2)) : MvPolynomial.X i ∈ I := by
    rcases i with ⟨i⟩
    fin_cases i
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC (a : k) : evalAtOrigin k (MvPolynomial.C a) = a :=
    (evalAtOriginAlgHom k).commutes a
  have hX₀ (i : ULift.{u} (Fin 2)) : evalAtOrigin k (MvPolynomial.X i) = 0 :=
    MvPolynomial.eval₂AlgHom_X _ _
  have h (p : coordinateRing k) : p - MvPolynomial.C (evalAtOrigin k p) ∈ I := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa only [hC, sub_self] using I.zero_mem
    | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul, hX₀, mul_zero, map_zero, sub_zero] using I.mul_mem_left p (hX i)
  apply le_antisymm
  · intro p hp
    have hp₀ : evalAtOrigin k p = 0 := hp
    simpa only [hp₀, map_zero, sub_zero] using h p
  · apply Ideal.span_le.mpr
    rintro p (rfl | rfl)
    · exact hX₀ _
    · exact hX₀ _

/-- The basic open `D(x)` in the affine plane. -/
@[stacks 01IL "punctured affine-plane X chart"]
abbrev chartX : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (xSection k)

/-- The basic open `D(y)` in the affine plane. -/
@[stacks 01IL "punctured affine-plane Y chart"]
abbrev chartY : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (ySection k)

/-- The basic open `D(xy)`. -/
@[stacks 01IL "punctured affine-plane overlap chart"]
abbrev chartXY : (affinePlane k).Opens :=
  (affinePlane k).basicOpen (xSection k * ySection k)

/-- The punctured affine plane, represented by `D(x) ∪ D(y)`. -/
@[stacks 01IL "punctured affine plane"]
abbrev puncturedOpen : (affinePlane k).Opens :=
  PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 2)) k

/-- The punctured affine plane is covered by `D(x)` and `D(y)`. -/
@[stacks 01IL "standard cover of the punctured affine plane"]
theorem puncturedOpen_eq_chartX_sup_chartY :
    puncturedOpen k = chartX k ⊔ chartY k := by
  change (⨆ i : ULift.{u} (Fin 2), (affinePlane k).basicOpen
    (PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k i)) = _
  rw [iSup_ulift]
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le
    · exact le_iSup (fun i : Fin 2 ↦ (affinePlane k).basicOpen
        (PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up i))) 0
    · exact le_iSup (fun i : Fin 2 ↦ (affinePlane k).basicOpen
        (PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k (ULift.up i))) 1

/-- The basic open `D(x)` is affine. -/
@[stacks 01IL "first affine chart of the punctured affine plane"]
theorem chartX_isAffineOpen : IsAffineOpen (chartX k) :=
  (isAffineOpen_top (affinePlane k)).basicOpen _

/-- The basic open `D(y)` is affine. -/
@[stacks 01IL "second affine chart of the punctured affine plane"]
theorem chartY_isAffineOpen : IsAffineOpen (chartY k) :=
  (isAffineOpen_top (affinePlane k)).basicOpen _

/-- The intersection `D(x) ∩ D(y)` is `D(xy)`. -/
@[stacks 01IL "intersection of the standard affine charts"]
theorem chartX_inf_chartY : chartX k ⊓ chartY k = chartXY k :=
  (Scheme.basicOpen_mul (affinePlane k) (xSection k) (ySection k)).symm

/-- The basic open `D(xy)` is affine. -/
@[stacks 01IL "affine overlap of the standard charts"]
theorem chartXY_isAffineOpen : IsAffineOpen (chartXY k) :=
  (isAffineOpen_top (affinePlane k)).basicOpen _

/-- The canonical map from `k[x,y]` to global sections of the punctured affine plane. -/
@[stacks 01IL "punctured-affine-plane global-sections comparison"]
noncomputable abbrev globalSectionsComparison :
    CommRingCat.of (coordinateRing k) ⟶
      Scheme.Γ.obj (Opposite.op (puncturedOpen k).toScheme) :=
  PuncturedAffineSpace.globalSectionsComparison (ULift.{u} (Fin 2)) k

namespace globalSectionsComparison

/-- The two-coordinate specialization of the punctured-affine global-sections comparison is an
isomorphism. -/
@[stacks 01IL "punctured affine-plane global sections"]
theorem isIso : IsIso (globalSectionsComparison k) := sorry

end globalSectionsComparison

private theorem coordinateModelIso_preimage_coordinate (i : ULift.{u} (Fin 2)) :
    (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen (MvPolynomial.X i) =
      (PuncturedAffinePlane.affinePlane k).basicOpen
        (PuncturedAffineSpace.coordinateSection (ULift.{u} (Fin 2)) k i) := by
  exact (congrArg (fun U : (PuncturedAffineSpace.coordinateSpectrum
      (ULift.{u} (Fin 2)) k).Opens ↦
      (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k).hom ⁻¹ᵁ U)
    (basicOpen_eq_of_affine (R := CommRingCat.of (PuncturedAffinePlane.coordinateRing k))
      (MvPolynomial.X i)).symm).trans
      (Scheme.preimage_basicOpen_top
        (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (PuncturedAffinePlane.coordinateRing k))).inv
          (MvPolynomial.X i)))

private theorem coordinateModelIso_inv_zeroSection :
    PuncturedAffineSpace.coordinateZeroSection (ULift.{u} (Fin 2)) k ≫
      (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k).inv =
    PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 2)) k := by
  have happ {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
      (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) :=
    congrArg (fun g : R ⟶ Γ(Spec S, ⊤) ↦ g r) (Scheme.ΓSpecIso_inv_naturality f).symm
  apply AffineSpace.hom_ext
  · simp only [PuncturedAffineSpace.coordinateZeroSection, PuncturedAffineSpace.evalAtOrigin,
      PuncturedAffineSpace.evalAtOriginAlgHom, AlgHom.toRingHom_eq_coe,
      PuncturedAffineSpace.coordinateModelIso, MvPolynomial.renameEquiv_symm, Iso.trans_inv,
      Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, RingEquiv.symm_mk,
      AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, Equiv.symm_symm, Scheme.Spec_map,
      Quiver.Hom.unop_op, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
      PuncturedAffineSpace.zeroSection, Scheme.Hom.isOver_iff, AffineSpace.homOfVector_over,
      CategoryTheory.over_def, comp_over, Spec.map_eq_id]
    ext a
    simp [MvPolynomial.renameEquiv_apply]
  · intro i
    simp only [PuncturedAffineSpace.coordinateModelIso, Iso.trans_inv,
      Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, PuncturedAffineSpace.zeroSection,
      AffineSpace.homOfVector_appTop_coord]
    erw [AffineSpace.SpecIso_inv_appTop_coord]
    change (Spec.map (CommRingCat.ofHom (PuncturedAffinePlane.evalAtOrigin k))).appTop
      ((Spec.map (MvPolynomial.renameEquiv k (Equiv.ulift :
        ULift.{u} (ULift.{u} (Fin 2)) ≃ ULift.{u} (Fin 2))).toRingEquiv.toCommRingCatIso.hom).appTop
          ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i))) = 0
    rw [happ, happ]
    simp [MvPolynomial.renameEquiv_apply]

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The origin point of the canonical affine plane. -/
@[stacks 01IL "origin"]
noncomputable abbrev origin : affinePlane k :=
  PuncturedAffineSpace.origin (ULift.{u} (Fin 2)) k

private theorem coordinateModelIso_hom_origin :
    (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k).hom
        (PuncturedAffinePlane.origin k) =
      PuncturedAffineSpace.coordinateOrigin (ULift.{u} (Fin 2)) k := by
  let e := PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k
  have hz : PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 2)) k ≫ e.hom =
      PuncturedAffineSpace.coordinateZeroSection (ULift.{u} (Fin 2)) k := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using (coordinateModelIso_inv_zeroSection k).symm
  change (PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 2)) k ≫ e.hom)
    (IsLocalRing.closedPoint k) = _
  rw [hz]
  apply PrimeSpectrum.ext
  change Ideal.comap (PuncturedAffinePlane.evalAtOrigin k) (IsLocalRing.maximalIdeal k) =
    PuncturedAffinePlane.originIdeal k
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

namespace puncturedOpen

/-- The punctured affine plane is the complement of its origin. -/
@[stacks 01IL "punctured affine plane as the complement of the origin"]
theorem coe_eq_compl_origin :
    (puncturedOpen k : Set (affinePlane k)) =
      ({origin k} : Set (affinePlane k))ᶜ := by
  let e := PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k
  haveI : (PuncturedAffinePlane.originIdeal k).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (PuncturedAffinePlane.evalAtOrigin k) (fun a ↦
      ⟨MvPolynomial.C a, (PuncturedAffinePlane.evalAtOriginAlgHom k).commutes a⟩)
  have hV : PrimeSpectrum.zeroLocus (PuncturedAffinePlane.originIdeal k :
      Set (PuncturedAffinePlane.coordinateRing k)) =
        {PuncturedAffineSpace.coordinateOrigin (ULift.{u} (Fin 2)) k} :=
    PrimeSpectrum.zeroLocus_eq_singleton _
  have hD : ((PrimeSpectrum.basicOpen (PuncturedAffinePlane.x k) ⊔
      PrimeSpectrum.basicOpen (PuncturedAffinePlane.y k)) :
        Set (PrimeSpectrum (PuncturedAffinePlane.coordinateRing k))) =
      {PuncturedAffineSpace.coordinateOrigin (ULift.{u} (Fin 2)) k}ᶜ := by
    rw [← hV, PuncturedAffinePlane.originIdeal_eq_span k, PrimeSpectrum.zeroLocus_span]
    ext q
    change (x k ∉ q.asIdeal ∨ y k ∉ q.asIdeal) ↔
      ¬ ({x k, y k} : Set (coordinateRing k)) ⊆ q.asIdeal
    rw [Set.insert_subset_iff, Set.singleton_subset_iff, not_and_or]
    rfl
  ext p
  change p ∈ PuncturedAffinePlane.puncturedOpen k ↔ p ≠ PuncturedAffinePlane.origin k
  have hp : p ∈ PuncturedAffinePlane.puncturedOpen k ↔
      e.hom p ∈ PrimeSpectrum.basicOpen (PuncturedAffinePlane.x k) ⊔
        PrimeSpectrum.basicOpen (PuncturedAffinePlane.y k) := by
    rw [PuncturedAffinePlane.puncturedOpen_eq_chartX_sup_chartY]
    change (p ∈ PuncturedAffinePlane.chartX k ∨ p ∈ PuncturedAffinePlane.chartY k) ↔ _
    exact or_congr
      (Iff.of_eq (congrArg (fun U : (PuncturedAffinePlane.affinePlane k).Opens ↦ p ∈ U)
        (coordinateModelIso_preimage_coordinate k (ULift.up 0))).symm)
      (Iff.of_eq (congrArg (fun U : (PuncturedAffinePlane.affinePlane k).Opens ↦ p ∈ U)
        (coordinateModelIso_preimage_coordinate k (ULift.up 1))).symm)
  rw [hp]
  change e.hom p ∈ ((PrimeSpectrum.basicOpen (PuncturedAffinePlane.x k) ⊔
      PrimeSpectrum.basicOpen (PuncturedAffinePlane.y k)) :
        Set (PrimeSpectrum (PuncturedAffinePlane.coordinateRing k))) ↔ _
  rw [hD]
  change e.hom p ≠ PuncturedAffineSpace.coordinateOrigin (ULift.{u} (Fin 2)) k ↔ _
  rw [← coordinateModelIso_hom_origin k]
  exact not_congr e.hom.homeomorph.injective.eq_iff

end puncturedOpen

/-- The punctured affine plane over a field is not affine. -/
@[stacks 01IL "nonaffineness"]
theorem not_isAffine : ¬ IsAffine (puncturedOpen k).toScheme := by
  intro h
  letI := h
  letI := PuncturedAffinePlane.globalSectionsComparison.isIso k
  haveI : IsIso (PuncturedAffinePlane.puncturedOpen k).ι.appTop :=
    (isIso_comp_left_iff
      (PuncturedAffineSpace.coordinateRingToGlobalSections (ULift.{u} (Fin 2)) k)
      (PuncturedAffinePlane.puncturedOpen k).ι.appTop).mp
        (PuncturedAffinePlane.globalSectionsComparison.isIso k)
  haveI : IsIso ((PuncturedAffinePlane.puncturedOpen k).ι ≫
      (PuncturedAffinePlane.affinePlane k).toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    infer_instance
  haveI : IsIso (PuncturedAffinePlane.puncturedOpen k).ι :=
    IsIso.of_isIso_comp_right
      (PuncturedAffinePlane.puncturedOpen k).ι (PuncturedAffinePlane.affinePlane k).toSpecΓ
  obtain ⟨z, hz⟩ := (PuncturedAffinePlane.puncturedOpen k).ι.homeomorph.surjective
    (PuncturedAffinePlane.origin k)
  have hz' : PuncturedAffinePlane.origin k ∈ PuncturedAffinePlane.puncturedOpen k := by
    rw [← hz]
    exact z.property
  rw [← SetLike.mem_coe, PuncturedAffinePlane.puncturedOpen.coe_eq_compl_origin] at hz'
  exact hz' (Set.mem_singleton _)

end Field
end PuncturedAffinePlane
end
end AlgebraicGeometry
