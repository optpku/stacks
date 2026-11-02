/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.Topology.Sheaves.Glue
import all ReasLib.Algebra.Category.Ring.Sheaf.Units

/-!
# Cartier divisor associated to an effective Cartier divisor

On an arbitrary scheme, an effective Cartier divisor determines a Cartier divisor
by gluing the local classes of its nonzerodivisor equations in `𝒦_S^⁎ / 𝒪_S^⁎`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

set_option backward.isDefEq.respectTransparency false in
private theorem unitsAddSheafValue_section (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat)
    {U : S.Opens} (g : (A.1.obj (op U))ˣ) :
    Sheaf.unitsAddSheafValue A (Sheaf.unitsAddSheafSection A g) = g.val := by
  dsimp only [Sheaf.unitsAddSheafSection, Sheaf.unitsAddSheafValue,
    Sheaf.unitsAddSheaf, Sheaf.unitsSheaf]
  exact Function.invFun_eq ⟨Additive.ofMul g, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem unitsAddSheafValue_injective (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat)
    {U : S.Opens} : Function.Injective (Sheaf.unitsAddSheafValue A (U := op U)) := by
  intro x y h
  dsimp only [Sheaf.unitsAddSheafValue, Sheaf.unitsAddSheaf, Sheaf.unitsSheaf] at h ⊢
  exact Units.ext h

set_option backward.isDefEq.respectTransparency false in
private theorem unitsAddSheafValue_add (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat)
    {U : S.Opens} (x y : (Sheaf.unitsAddSheaf A).1.obj (op U)) :
    Sheaf.unitsAddSheafValue A (x + y) =
      Sheaf.unitsAddSheafValue A x * Sheaf.unitsAddSheafValue A y := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unitsAddSheafValue_restrict (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat)
    {U V : S.Opens} (i : V ⟶ U) (g : (Sheaf.unitsAddSheaf A).1.obj (op U)) :
    Sheaf.unitsAddSheafValue A ((Sheaf.unitsAddSheaf A).1.map i.op g) =
      A.1.map i.op (Sheaf.unitsAddSheafValue A g) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unitsAddSheafUnit_section (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat)
    {U : S.Opens} (g : (A.1.obj (op U))ˣ) :
    Sheaf.unitsAddSheafUnit A (Sheaf.unitsAddSheafSection A g) = g := by
  have hinj : Function.Injective (Sheaf.unitsAddSheafSection A (U := op U)) := by
    intro a b h
    apply Units.ext
    exact (unitsAddSheafValue_section A a).symm.trans
      ((congrArg (Sheaf.unitsAddSheafValue A) h).trans (unitsAddSheafValue_section A b))
  exact Function.leftInverse_invFun hinj g

/-- The local Cartier class of a meromorphic unit on an open `U`. -/
def ofMeromorphicUnitsOn (U : S.Opens)
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ) :
    (cartierDivisorAddSheaf S).1.obj (op U) :=
  ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
      (op U)).hom
    (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f)

/-- `ofMeromorphicUnitsOn` is the `U`-component of the cokernel projection on a meromorphic
unit. -/
theorem ofMeromorphicUnitsOn_eq (U : S.Opens)
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ) :
    ofMeromorphicUnitsOn U f =
      ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
          (op U)).hom
        (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f) :=
  rfl

/-- Global `ofMeromorphicUnits` is the `U = ⊤` case of `ofMeromorphicUnitsOn`. -/
theorem ofMeromorphicUnits_eq_ofMeromorphicUnitsOn_top
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    ofMeromorphicUnits S f = ofMeromorphicUnitsOn (⊤ : S.Opens) f :=
  rfl

/-- A nonzerodivisor on an affine open is a meromorphic-function denominator. -/
theorem mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors
    (U : S.affineOpens) (f : Γ(S, U)) (hf : f ∈ nonZeroDivisors (Γ(S, U))) :
    f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op (U : S.Opens)) := by
  change f ∈ ⨅ x : (U : S.Opens),
    (nonZeroDivisors (S.presheaf.stalk x.1)).comap
      (S.presheaf.germ (U : S.Opens) x.1 x.2).hom
  simp only [Submonoid.mem_iInf, Submonoid.mem_comap]
  intro x
  letI := U.2.isLocalization_stalk x
  exact IsLocalization.nonZeroDivisors_le_comap
    (U.2.primeIdealOf x).asIdeal.primeCompl (S.presheaf.stalk x.1) hf

/-- The meromorphic unit on `U` represented by a meromorphic-function denominator. -/
def meromorphicUnitOfDenominator {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ :=
  let G := S.toLocallyRingedSpace.meromorphicFunctionDenominators
  Units.map
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology S.toTopCat)
          G.localizationPresheaf).app (op U)).hom.toMonoidHom
    (IsLocalization.map_units (G.localizationPresheaf.obj (op U)) ⟨f, hf⟩).unit

set_option backward.isDefEq.respectTransparency false in
private theorem meromorphicUnitOfDenominator_val {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    (meromorphicUnitOfDenominator f hf).val =
      ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)) f := by
  simp only [meromorphicUnitOfDenominator, Units.coe_map, IsUnit.unit_spec]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (toSheafify_naturality (Opens.grothendieckTopology S.toTopCat)
        S.presheaf.toTotalQuotientPresheaf) (op U)) f

/-- The local Cartier class of a meromorphic-function denominator, viewed as a meromorphic
unit. -/
def ofNonZeroDivisor {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    (cartierDivisorAddSheaf S).1.obj (op U) :=
  ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator f hf)

/-- `ofNonZeroDivisor` is the local Cartier class of the associated meromorphic unit. -/
theorem ofNonZeroDivisor_eq {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    ofNonZeroDivisor f hf = ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator f hf) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ofNonZeroDivisor_restrict {U V : S.Opens} (i : V ⟶ U) (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    (cartierDivisorAddSheaf S).1.map i.op (ofNonZeroDivisor f hf) =
      ofNonZeroDivisor (S.presheaf.map i.op f)
        (S.toLocallyRingedSpace.meromorphicFunctionDenominators.map i.op hf) := by
  unfold ofNonZeroDivisor ofMeromorphicUnitsOn
  refine ((cokernel.π (Sheaf.unitsAddMap
    S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.naturality_apply
      i.op (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf
        (meromorphicUnitOfDenominator f hf))).symm.trans ?_
  apply congrArg ((cokernel.π (Sheaf.unitsAddMap
    S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app (op V))
  apply unitsAddSheafValue_injective
  rw [unitsAddSheafValue_restrict, unitsAddSheafValue_section, unitsAddSheafValue_section]
  simp only [meromorphicUnitOfDenominator_val]
  exact (S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom.naturality_apply i.op f).symm

set_option backward.isDefEq.respectTransparency false in
private theorem ofMeromorphicUnitsOn_mul {U : S.Opens}
    (f g : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ) :
    ofMeromorphicUnitsOn U (f * g) = ofMeromorphicUnitsOn U f + ofMeromorphicUnitsOn U g := by
  let q := ((cokernel.π
    (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app (op U)).hom
  change q (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf (f * g)) =
    q (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f) +
      q (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf g)
  refine (congrArg q ?_).trans (q.map_add _ _)
  apply unitsAddSheafValue_injective
  rw [unitsAddSheafValue_section, unitsAddSheafValue_add,
    unitsAddSheafValue_section, unitsAddSheafValue_section]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ofMeromorphicUnitsOn_structureUnit {U : S.Opens} (g : Γ(S, U)ˣ) :
    ofMeromorphicUnitsOn U
      (Units.map ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)).hom.toMonoidHom g) = 0 := by
  have h := congrArg (fun k => ((k.hom.app (op U)).hom (Sheaf.unitsAddSheafSection S.sheaf g)))
    (unitsAddMap_toMeromorphic_comp_π S)
  change ((cokernel.π
      (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
        (op U)).hom
      (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf
        (Units.map ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)).hom.toMonoidHom
          (Sheaf.unitsAddSheafUnit S.sheaf (Sheaf.unitsAddSheafSection S.sheaf g)))) = 0 at h
  rw [unitsAddSheafUnit_section (S := S) S.sheaf g] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem mem_nonZeroDivisors_of_denominator {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U)) :
    f ∈ nonZeroDivisors Γ(S, U) := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
  intro a ha
  apply TopCat.Presheaf.section_ext S.sheaf U
  intro x hx
  rw [map_zero]
  apply (Submonoid.mem_iInf.mp hf ⟨x, hx⟩).2
  change (S.presheaf.germ U x hx).hom a * (S.presheaf.germ U x hx).hom f = 0
  rw [← map_mul, ha, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem ofNonZeroDivisor_eq_zero_of_isUnit {U : S.Opens} (f : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))
    (hunit : IsUnit f) : ofNonZeroDivisor f hf = 0 := by
  have h : meromorphicUnitOfDenominator f hf =
      Units.map ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)).hom.toMonoidHom hunit.unit := by
    apply Units.ext
    simp only [Units.coe_map, meromorphicUnitOfDenominator_val, hunit.unit_spec]
    rfl
  change ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator f hf) = 0
  rw [h, ofMeromorphicUnitsOn_structureUnit]

set_option backward.isDefEq.respectTransparency false in
/-- Two meromorphic-function denominators generating the same principal ideal determine the
same local Cartier class. -/
theorem ofNonZeroDivisor_eq_of_span_eq {U : S.Opens} (f g : Γ(S, U))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))
    (hg : g ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))
    (hspan : Ideal.span ({f} : Set (Γ(S, U))) = Ideal.span ({g} : Set (Γ(S, U)))) :
    ofNonZeroDivisor f hf = ofNonZeroDivisor g hg := by
  obtain ⟨a, ha⟩ := Ideal.span_singleton_le_span_singleton.mp hspan.ge
  obtain ⟨b, hb⟩ := Ideal.span_singleton_le_span_singleton.mp hspan.le
  have hfreg := (isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_denominator f hf)).1
  have hab : a * b = 1 := hfreg (by
    change f * (a * b) = f * 1
    rw [← mul_assoc, ← ha, ← hb, mul_one])
  let v : Γ(S, U)ˣ := ⟨a, b, hab, by simpa only [mul_comm] using hab⟩
  have hv : meromorphicUnitOfDenominator g hg = meromorphicUnitOfDenominator f hf *
      Units.map ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)).hom.toMonoidHom v := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, meromorphicUnitOfDenominator_val]
    change ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)) g =
      ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)) f *
        ((S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).hom.app (op U)) a
    rw [ha, map_mul]
  symm
  change ofMeromorphicUnitsOn U (meromorphicUnitOfDenominator g hg) = _
  rw [hv, ofMeromorphicUnitsOn_mul, ofMeromorphicUnitsOn_structureUnit, add_zero]
  rfl

/-- An affine local equation consists of an affine open and a specified nonzerodivisor
that generates the ideal of the divisor there. -/
def effectiveCartierLocalEquation (D : S.IdealSheafData) : Type u :=
  Σ U : S.affineOpens,
    {f : Γ(S, U) //
      f ∈ nonZeroDivisors (Γ(S, U)) ∧ D.ideal U = Ideal.span ({f} : Set (Γ(S, U)))}

/-- The open family formed by the support complement and every affine open equipped with
a nonzerodivisor equation for the divisor. -/
def effectiveCartierCover (D : S.IdealSheafData) :
    Option (effectiveCartierLocalEquation D) → S.Opens :=
  fun i ↦
    match i with
    | none => D.support.compl
    | some e => (e.1 : S.Opens)

/-- The support complement and all affine nonzerodivisor equations of an effective Cartier
divisor cover the scheme. -/
theorem effectiveCartierCover_sup (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    (⊤ : S.Opens) ≤ iSup (effectiveCartierCover D) := by
  classical
  intro x _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_cases hx : x ∈ D.support
  · obtain ⟨U, hxU, f, hf, hgen⟩ :=
      D.exists_affineOpen_nonZeroDivisor_generator inferInstance hx
    exact ⟨some ⟨U, ⟨f, hf, hgen⟩⟩, hxU⟩
  · exact ⟨none, hx⟩

/-- The local Cartier sections are zero on the support complement and the class of the
specified generator on each indexed affine open. -/
def effectiveCartierLocalSection (D : S.IdealSheafData) :
    ∀ i, (cartierDivisorAddSheaf S).1.obj (op (effectiveCartierCover D i)) :=
  fun i ↦
    match i with
    | none => 0
    | some e =>
      ofNonZeroDivisor e.2.1
        (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors e.1 e.2.1 e.2.2.1)

set_option backward.isDefEq.respectTransparency false in
private theorem cartierSection_ext {U : S.Opens}
    (s t : (cartierDivisorAddSheaf S).1.obj (op U))
    (h : ∀ (V : S.affineOpens) (hVU : (V : S.Opens) ≤ U),
      (cartierDivisorAddSheaf S).1.map (homOfLE hVU).op s =
        (cartierDivisorAddSheaf S).1.map (homOfLE hVU).op t) : s = t := by
  apply TopCat.Presheaf.section_ext (cartierDivisorAddSheaf S) U
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
  simpa only [TopCat.Presheaf.germ_res_apply] using
    congrArg (TopCat.Presheaf.germ (cartierDivisorAddSheaf S).1 V x hxV) (h ⟨V, hV⟩ hVU)

set_option backward.isDefEq.respectTransparency false in
private theorem ideal_eq_top_of_subset_support_compl (D : S.IdealSheafData) (U : S.affineOpens)
    (hU : (U : S.Opens) ≤ D.support.compl) : D.ideal U = ⊤ := by
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  apply (Set.image_eq_empty (f := U.2.fromSpec)).mp
  rw [U.2.fromSpec_image_zeroLocus, ← D.coe_support_inter]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hU hx.2 hx.1

set_option backward.isDefEq.respectTransparency false in
private theorem effectiveCartierLocalSection_restrict (D : S.IdealSheafData)
    (i : Option (effectiveCartierLocalEquation D)) (V : S.affineOpens)
    (hV : (V : S.Opens) ≤ effectiveCartierCover D i) (f : Γ(S, V))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op (V : S.Opens)))
    (hgen : D.ideal V = Ideal.span ({f} : Set Γ(S, V))) :
    (cartierDivisorAddSheaf S).1.map (homOfLE hV).op
        (effectiveCartierLocalSection D i) = ofNonZeroDivisor f hf := by
  cases i with
  | none =>
      change (cartierDivisorAddSheaf S).1.map (homOfLE hV).op 0 = _
      rw [map_zero]
      symm
      apply ofNonZeroDivisor_eq_zero_of_isUnit
      apply Ideal.span_singleton_eq_top.mp
      rw [← hgen]
      exact ideal_eq_top_of_subset_support_compl D V hV
  | some e =>
      change (cartierDivisorAddSheaf S).1.map (homOfLE hV).op
        (ofNonZeroDivisor e.2.1
          (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors e.1 e.2.1 e.2.2.1)) = _
      rw [ofNonZeroDivisor_restrict]
      apply ofNonZeroDivisor_eq_of_span_eq
      calc
        _ = D.ideal V := by
          have hm := D.map_ideal hV
          simp only [e.2.2.2, Ideal.map_span, Set.image_singleton] at hm
          exact hm
        _ = _ := hgen

set_option backward.isDefEq.respectTransparency false in
/-- The local Cartier classes on the standard cover of an effective Cartier divisor are
compatible. -/
theorem effectiveCartierLocalSection_compatible (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    TopCat.Presheaf.IsCompatible (cartierDivisorAddSheaf S).1 (effectiveCartierCover D)
      (effectiveCartierLocalSection D) := by
  intro i j
  apply cartierSection_ext
  intro V hV
  let hi : (V : S.Opens) ≤ effectiveCartierCover D i := hV.trans inf_le_left
  let hj : (V : S.Opens) ≤ effectiveCartierCover D j := hV.trans inf_le_right
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change (cartierDivisorAddSheaf S).1.map (homOfLE hi).op
      (effectiveCartierLocalSection D i) =
    (cartierDivisorAddSheaf S).1.map (homOfLE hj).op
      (effectiveCartierLocalSection D j)
  obtain ⟨f, hf, hgen⟩ : ∃ (f : Γ(S, V))
      (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op (V : S.Opens))),
      D.ideal V = Ideal.span ({f} : Set Γ(S, V)) := by
    cases i with
    | none =>
        refine ⟨1, (S.toLocallyRingedSpace.meromorphicFunctionDenominators.obj _).one_mem, ?_⟩
        rw [ideal_eq_top_of_subset_support_compl D V hi, Ideal.span_singleton_one]
    | some e =>
        refine ⟨S.presheaf.map (homOfLE hi).op e.2.1,
          S.toLocallyRingedSpace.meromorphicFunctionDenominators.map (homOfLE hi).op
            (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors e.1 e.2.1 e.2.2.1), ?_⟩
        have hm := (D.map_ideal hi).symm
        simp only [e.2.2.2, Ideal.map_span, Set.image_singleton] at hm
        exact hm
  rw [effectiveCartierLocalSection_restrict D i V hi f hf hgen, effectiveCartierLocalSection_restrict D j V hj f hf hgen]

set_option backward.isDefEq.respectTransparency false in
private theorem glueCartierSection_spec (F : TopCat.Sheaf AddCommGrpCat.{u} S.toTopCat) {ι : Type u}
    (U : ι → S.Opens) (V : S.Opens) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s : ∀ i, F.1.obj (op (U i))) (hs : TopCat.Presheaf.IsCompatible F.1 U s) (i : ι) :
    F.1.map (iUV i).op (F.glueOfCompatibleFamily U V iUV hcover s hs) = s i := by
  let P := F.1 ⋙ CategoryTheory.forget AddCommGrpCat
  have hP : TopCat.Presheaf.IsSheaf P :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget AddCommGrpCat) F.1).mp F.property
  let t := (hP.isSheafPairwiseIntersections U).some
  let compatibleSection := TopCat.Presheaf.IsCompatible.sectionPairwise (F := P) hs
  have h := ConcreteCategory.congr_hom (t.fac (Types.coneOfSection compatibleSection.property)
    (op (CategoryTheory.Pairwise.single i))) PUnit.unit
  unfold TopCat.Sheaf.glueOfCompatibleFamily
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

/-- The Cartier divisor associated to an effective Cartier divisor, obtained by gluing the
local classes of its nonzerodivisor equations. -/
def cartierDivisor_ofEffectiveCartier (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : CartierDivisor S :=
  TopCat.Sheaf.glueOfCompatibleFamily (cartierDivisorAddSheaf S) (effectiveCartierCover D) ⊤
    (fun _ ↦ homOfLE le_top) (effectiveCartierCover_sup D)
    (effectiveCartierLocalSection D) (effectiveCartierLocalSection_compatible D)

/-- On an affine open where `D` is cut out by a nonzerodivisor `f`, the associated Cartier
divisor restricts to the local class of `f`. -/
theorem cartierDivisor_ofEffectiveCartier_spec (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (U : S.affineOpens) (f : Γ(S, U))
    (hf : f ∈ nonZeroDivisors (Γ(S, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(S, U)))) :
    (cartierDivisorAddSheaf S).1.map (homOfLE (le_top : (U : S.Opens) ≤ ⊤)).op
        (cartierDivisor_ofEffectiveCartier D) =
      ofNonZeroDivisor f
        (mem_meromorphicFunctionDenominators_of_mem_nonZeroDivisors U f hf) := by
  exact glueCartierSection_spec (cartierDivisorAddSheaf S)
    (effectiveCartierCover D) ⊤ (fun _ ↦ homOfLE le_top) (effectiveCartierCover_sup D)
    (effectiveCartierLocalSection D) (effectiveCartierLocalSection_compatible D)
    (some ⟨U, ⟨f, hf, hgen⟩⟩)

/-- The Cartier divisor associated to an effective Cartier divisor vanishes on the open
complement of its support. -/
theorem cartierDivisor_ofEffectiveCartier_eq_zero_on_complement (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    (cartierDivisorAddSheaf S).1.map
        (homOfLE (le_top : D.support.compl ≤ ⊤)).op
        (cartierDivisor_ofEffectiveCartier D) =
      0 := by
  exact glueCartierSection_spec (cartierDivisorAddSheaf S)
    (effectiveCartierCover D) ⊤ (fun _ ↦ homOfLE le_top) (effectiveCartierCover_sup D)
    (effectiveCartierLocalSection D) (effectiveCartierLocalSection_compatible D) none

set_option backward.isDefEq.respectTransparency false in
/-- If an effective Cartier divisor is globally generated by a meromorphic-function
denominator, the associated Cartier divisor is the class of that denominator. -/
theorem cartierDivisor_ofEffectiveCartier_of_span_top (D : S.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (f : Γ(S, ⊤))
    (hf : f ∈ (S.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op ⊤))
    (hgen : ∀ U : S.affineOpens,
      D.ideal U =
        Ideal.span
          ({S.presheaf.map (homOfLE (le_top : (U : S.Opens) ≤ ⊤)).op f} : Set (Γ(S, U)))) :
    cartierDivisor_ofEffectiveCartier D = ofNonZeroDivisor f hf := by
  apply cartierSection_ext
  intro U hU
  rw [ofNonZeroDivisor_restrict]
  exact cartierDivisor_ofEffectiveCartier_spec D U
    (S.presheaf.map (homOfLE hU).op f)
    (mem_nonZeroDivisors_of_denominator _
      (S.toLocallyRingedSpace.meromorphicFunctionDenominators.map (homOfLE hU).op hf))
    (hgen U)

end AlgebraicGeometry.Scheme
