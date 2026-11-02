/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length

/-!
# Length over an Artinian local ring

Over an Artinian local ring, composition length identifies the finite-module Grothendieck group
with `ℤ`.  This leaf keeps that local specialization beside the general length homomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]

/-
API design: `finiteLength` remains the Artinian-general map.  Locality is introduced only for
its inverse: an integer is sent to that multiple of the residue-field class.  The explicit inverse
and both inverse laws make the resulting `AddEquiv` symmetric and keep consumers independent of
the chosen inverse hidden inside `AddEquiv.ofBijective`.  The source works in one universe; a
cross-universe statement would require a separate Grothendieck-group change-of-universe
comparison, so it is not asserted here.
-/

namespace Finite

/-- The class of the residue field in the finite-module Grothendieck group. -/
@[stacks 00JI "residue-field class in finite-module K0"]
def residueFieldClass : finite.{u, u} R :=
  finiteClass R (IsLocalRing.ResidueField R)

/-- The additive map sending an integer to that multiple of the residue-field class. -/
@[stacks 00JI "virtual residue-field classes in finite-module K0"]
def ofLength : ℤ →+ finite.{u, u} R :=
  zmultiplesHom _ (residueFieldClass R)

/-- The virtual residue-field class of length one is the residue-field class. -/
@[simp]
theorem ofLength_one : ofLength R 1 = residueFieldClass R :=
  one_zsmul (residueFieldClass R)

end Finite

/-- Composition length sends the residue-field class to `1`. -/
@[stacks 00JI "length of the residue-field class", simp]
theorem finiteLength_residueFieldClass :
    finiteLength R (Finite.residueFieldClass R) = 1 := by
  have : IsSimpleModule R (IsLocalRing.ResidueField R) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal R).1
  change finiteLength R (finiteClass R (IsLocalRing.ResidueField R)) = 1
  rw [finiteLength_finiteClass, Module.length_eq_one]
  rfl

/-- Taking length after forming a virtual residue-field class recovers the integer. -/
@[stacks 00JI "length of virtual residue-field classes", simp]
theorem finiteLength_ofLength (n : ℤ) :
    finiteLength R (Finite.ofLength R n) = n := by
  change finiteLength R (n • Finite.residueFieldClass R) = n
  rw [map_zsmul, finiteLength_residueFieldClass]
  simp

namespace Finite

private theorem finiteClass_eq_length_smul
    {M : Type u} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∀ [Module.Finite R M],
      finiteClass R M = (Module.length R M).toNat • residueFieldClass R := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    intro
    calc
      finiteClass R M = 0 := of_subsingleton R (FGModuleCat.of R M)
      _ = (Module.length R M).toNat • residueFieldClass R := by simp
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro
    haveI : IsNoetherian R N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
    haveI : IsArtinian R N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
    have hQ : finiteClass R (M ⧸ N) = residueFieldClass R := by
      obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
        (inferInstance : IsSimpleModule R (M ⧸ N))
      have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
      subst I
      exact of_iso R (P := ModuleCat.isFG R)
        (by change Module.Finite R PUnit; infer_instance) e.toFGModuleCatIso
    let S : ShortComplex (FGModuleCat R) :=
      ShortComplex.mk (FGModuleCat.ofHom N.subtype) (FGModuleCat.ofHom N.mkQ)
        (by
          apply FGModuleCat.hom_ext
          change N.mkQ.comp N.subtype = 0
          exact (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero)
    have hS : (S.map (ModuleCat.isFG R).ι).ShortExact := by
      apply ModuleCat.shortComplex_shortExact
      · exact LinearMap.exact_subtype_mkQ N
      · exact N.injective_subtype
      · exact N.mkQ_surjective
    have hadd : finiteClass R M = finiteClass R N + finiteClass R (M ⧸ N) :=
      ObjectProperty.GrothendieckGroup.of_shortExact S hS
    have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one R (M ⧸ N)] at hlen
    rw [hadd, ih, hQ, hlen, ENat.toNat_add Module.length_ne_top (by simp)]
    simp [add_nsmul]

/-- The virtual residue-field class determined by the length of a finite-module class is that
class. -/
@[stacks 00JI "finite-module classes are determined by length", simp]
theorem ofLength_finiteLength (x : finite.{u, u} R) :
    ofLength R (finiteLength R x) = x := by
  have hgen (M : FGModuleCat.{u} R) :
      ofLength R (finiteLength R (finiteOf R M)) = finiteOf R M := by
    rw [finiteLength_finiteOf]
    change ((Module.length R M.obj).toNat : ℤ) • residueFieldClass R = finiteOf R M
    rw [natCast_zsmul]
    exact (finiteClass_eq_length_smul R
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)).symm
  refine QuotientAddGroup.induction_on x ?_
  intro a
  change ofLength R (finiteLength R ((QuotientAddGroup.mk' _) a)) =
    (QuotientAddGroup.mk' _) a
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of M => exact hgen M
  | neg M ih => simpa only [map_neg] using congrArg Neg.neg ih
  | add a b ha hb => simpa only [map_add, ha, hb]

end Finite

/-- The explicit length identification of the finite-module Grothendieck group of an Artinian
local ring with `ℤ`. -/
@[stacks 00JI "local finite-module Grothendieck group length equivalence"]
def finiteLengthEquiv : finite.{u, u} R ≃+ ℤ where
  toFun := finiteLength R
  invFun := Finite.ofLength R
  left_inv := Finite.ofLength_finiteLength R
  right_inv := finiteLength_ofLength R
  map_add' := (finiteLength R).map_add

/-- Lemma 10.55.7 (Tag 00JI): over an Artinian local ring, the length map on the finite-module
Grothendieck group is an isomorphism. -/
@[stacks 00JI "length is an isomorphism on the local finite-module Grothendieck group"]
theorem finiteLength_bijective :
    Function.Bijective ((finiteLength R) : finite.{u, u} R → ℤ) :=
  (finiteLengthEquiv R).bijective

/-- The local length equivalence evaluates by the canonical length homomorphism. -/
@[stacks 00JI "local length equivalence evaluation", simp]
theorem finiteLengthEquiv_apply (x : finite.{u, u} R) :
    finiteLengthEquiv R x = finiteLength R x := rfl

/-- The inverse local length equivalence forms the corresponding virtual residue-field class. -/
@[stacks 00JI "inverse local length equivalence evaluation", simp]
theorem finiteLengthEquiv_symm_apply (n : ℤ) :
    (finiteLengthEquiv R).symm n = Finite.ofLength R n := rfl

end CategoryTheory.ModuleCat.K0
