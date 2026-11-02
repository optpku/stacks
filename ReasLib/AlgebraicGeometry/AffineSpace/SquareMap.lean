/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.AlgebraicGeometry.AffineSpace.MorphismProperties

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The endomorphism of the affine line over `Spec (.of k)` that squares its coordinate. -/
def squareMap (k : Type u) [Field k] :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  homOfVector (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) fun i ↦
    coord (Spec (.of k)) i ^ 2

/-- Pullback by the squaring endomorphism sends the affine-line coordinate to its square. -/
theorem squareMap_appTop_coord (k : Type u) [Field k] :
    (squareMap k).appTop (coord (Spec (.of k)) (ULift.up (0 : Fin 1))) =
      coord (Spec (.of k)) (ULift.up (0 : Fin 1)) ^ 2 := by
  simp [squareMap]

/-- The squaring endomorphism commutes with the affine-line projection to its base. -/
theorem squareMap_over (k : Type u) [Field k] :
    squareMap k ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) =
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) := by
  simp [squareMap]

/-- The standard identification of the affine line with the spectrum of `k[X]`. -/
private def squareMapLineIso (k : Type u) [Field k] :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ≅ Spec (.of (Polynomial k)) :=
  SpecIso (ULift.{u} (Fin 1)) (.of k) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).symm.toRingEquiv.toCommRingCatIso.op

private theorem squareMapLineIso_inv_over (k : Type u) [Field k] :
    (squareMapLineIso k).inv ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  simp only [squareMapLineIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc, SpecIso_inv_over,
    ← Spec.map_comp]
  congr 1
  ext a
  simp [MvPolynomial.uniqueAlgEquiv]

private theorem squareMapLineIso_inv_appTop_coord (k : Type u) [Field k]
    (i : ULift.{u} (Fin 1)) :
    (squareMapLineIso k).inv.appTop (coord (Spec (.of k)) i) =
      (Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X := by
  change (Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingHom)).appTop
    ((SpecIso (ULift.{u} (Fin 1)) (.of k)).inv.appTop
      (coord (Spec (.of k)) i)) = _
  rw [SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

private theorem squareMap_eq_specMap_expand (k : Type u) [Field k] :
    squareMap k = (squareMapLineIso k).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.expand k 2).toRingHom) ≫ (squareMapLineIso k).inv := by
  rw [← Iso.inv_comp_eq]
  apply hom_ext
  · simp only [Category.assoc, squareMap_over, squareMapLineIso_inv_over,
      ← Spec.map_comp]
    congr 1
    ext a
    simp
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      squareMap, homOfVector_appTop_coord, map_pow,
      squareMapLineIso_inv_appTop_coord]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    simp

private theorem squareExpand_integral (k : Type u) [Field k] :
    (Polynomial.expand k 2).toRingHom.IsIntegral := by
  let f := (Polynomial.expand k 2).toRingHom
  letI := f.toAlgebra
  have hX : _root_.IsIntegral (Polynomial k) (Polynomial.X : Polynomial k) := by
    apply _root_.IsIntegral.of_pow (n := 2) (by decide)
    change f.IsIntegralElem (Polynomial.X ^ 2)
    simpa [f] using (f.isIntegralElem_map (x := (Polynomial.X : Polynomial k)))
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact RingHom.IsIntegralElem.add f hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    have hC : f.IsIntegralElem (Polynomial.C a) := by
      simpa [f] using (f.isIntegralElem_map (x := Polynomial.C a))
    exact RingHom.IsIntegralElem.mul f hC (hX.pow n)

private theorem squareExpand_flat (k : Type u) [Field k] :
    (Polynomial.expand k 2).toRingHom.Flat := by
  let f := (Polynomial.expand k 2).toRingHom
  letI := f.toAlgebra
  letI : Module (Polynomial k) (Polynomial k) := (f.toAlgebra).toModule
  haveI : Module.IsTorsionFree (Polynomial k) (Polynomial k) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (Polynomial.expand_injective (R := k) (by decide : 0 < 2))
  change Module.Flat (Polynomial k) (Polynomial k)
  infer_instance

private theorem squareExpand_finiteType (k : Type u) [Field k] :
    (Polynomial.expand k 2).toRingHom.FiniteType := by
  let f := (Polynomial.expand k 2).toRingHom
  have hC : (Polynomial.C : k →+* Polynomial k).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have heq : f.comp Polynomial.C = Polynomial.C := by
    ext a
    simp [f]
  exact RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C)
    (heq.symm ▸ hC)

/-- An infinitesimal lift over the dual numbers would give an element of square `ε`
whose constant term is zero, whereas every such element has square zero. -/
private theorem squareExpand_not_smooth (k : Type u) [Field k] :
    ¬ (Polynomial.expand k 2).toRingHom.Smooth := by
  intro h
  let f := (Polynomial.expand k 2).toRingHom
  letI := f.toAlgebra
  haveI : Algebra.FormallySmooth (Polynomial k) (Polynomial k) :=
    (RingHom.smooth_def.mp h).1.toAlgebra
  let e : Polynomial k →+* k := Polynomial.evalRingHom 0
  let d : Polynomial k →+* TrivSqZeroExt k k :=
    (Polynomial.aeval (TrivSqZeroExt.inr (1 : k))).toRingHom
  letI : Algebra (Polynomial k) k := e.toAlgebra
  letI : Algebra (Polynomial k) (TrivSqZeroExt k k) := d.toAlgebra
  have he : e.comp f = e := by
    ext a <;> simp [e, f]
  let q : Polynomial k →ₐ[Polynomial k] k :=
    { e with commutes' := fun r => DFunLike.congr_fun he r }
  have hd : (TrivSqZeroExt.fstHom k k k).toRingHom.comp d = e := by
    ext a <;> simp [e, d, Polynomial.aeval_def]
  let p : TrivSqZeroExt k k →ₐ[Polynomial k] k :=
    { (TrivSqZeroExt.fstHom k k k).toRingHom with
      commutes' := fun r => DFunLike.congr_fun hd r }
  have hp : Function.Surjective p := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hnil : IsNilpotent (RingHom.ker p.toRingHom) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩
  let l := Algebra.FormallySmooth.liftOfSurjective q p hp hnil
  have hfst : (l Polynomial.X).fst = 0 := by
    calc
      (l Polynomial.X).fst = p (l Polynomial.X) := rfl
      _ = q Polynomial.X :=
        Algebra.FormallySmooth.liftOfSurjective_apply q p hp hnil Polynomial.X
      _ = 0 := by simp [q, e]
  have hl : l Polynomial.X ^ 2 = TrivSqZeroExt.inr (1 : k) := by
    have hl := l.commutes (Polynomial.X : Polynomial k)
    change l (f Polynomial.X) = d Polynomial.X at hl
    simpa [f, d] using hl
  have hzero : l Polynomial.X ^ 2 = 0 := by
    apply TrivSqZeroExt.ext <;>
      simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hfst]
  have hbad := congrArg TrivSqZeroExt.snd (hl.symm.trans hzero)
  simpa using hbad

/-- The squaring endomorphism of the affine line over a field is surjective. -/
instance squareMap_surjective (k : Type u) [Field k] : Surjective (squareMap k) := by
  rw [squareMap_eq_specMap_expand]
  haveI : Surjective (Spec.map (CommRingCat.ofHom (Polynomial.expand k 2).toRingHom)) :=
    ⟨(squareExpand_integral k).comap_surjective
      (Polynomial.expand_injective (R := k) (by decide : 0 < 2))⟩
  infer_instance

/-- The squaring endomorphism of the affine line over a field is flat. -/
instance squareMap_flat (k : Type u) [Field k] : Flat (squareMap k) := by
  rw [squareMap_eq_specMap_expand]
  haveI : Flat (Spec.map (CommRingCat.ofHom (Polynomial.expand k 2).toRingHom)) :=
    Flat.SpecMap_iff.mpr (squareExpand_flat k)
  infer_instance

/-- The squaring endomorphism of the affine line over a field is locally of finite presentation. -/
instance squareMap_locallyOfFinitePresentation (k : Type u) [Field k] :
    LocallyOfFinitePresentation (squareMap k) := by
  rw [squareMap_eq_specMap_expand]
  haveI : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Polynomial.expand k 2).toRingHom)) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.FinitePresentation.of_finiteType.mp (squareExpand_finiteType k))
  infer_instance

/-- The squaring endomorphism of the affine line over a field is not smooth. -/
theorem squareMap_not_smooth (k : Type u) [Field k] : ¬ Smooth (squareMap k) := by
  rw [squareMap_eq_specMap_expand, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth),
    MorphismProperty.cancel_right_of_respectsIso (P := @Smooth)]
  exact fun h => squareExpand_not_smooth k
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

/-- The squaring endomorphism of the affine line over a field is universally closed. -/
instance squareMap_universallyClosed (k : Type u) [Field k] :
    UniversallyClosed (squareMap k) := by
  rw [squareMap_eq_specMap_expand]
  haveI : IsIntegralHom (Spec.map (CommRingCat.ofHom (Polynomial.expand k 2).toRingHom)) :=
    IsIntegralHom.SpecMap_iff.mpr (squareExpand_integral k)
  infer_instance

end AlgebraicGeometry.AffineSpace
