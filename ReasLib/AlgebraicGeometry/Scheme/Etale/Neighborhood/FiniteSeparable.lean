/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.RingTheory.RingHom.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.ResidueField
public import ReasLib.RingTheory.Etale.Point.FiniteSeparable

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/-- Every finite separable extension of the residue field at a point of a
scheme is realized by the residue field at the selected point of an étale
neighbourhood. -/
@[stacks 02LF]
theorem exists_residueFieldEquiv (S : Scheme.{u}) (s : S)
    (k : Type v) [Field k] [Algebra (S.residueField s) k]
    [FiniteDimensional (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ U : EtaleNeighborhood S s,
      Nonempty (U.toEtale.left.residueField U.point ≃ₐ[S.residueField s] k) := by
  classical
  -- Choose a point only from the native affine cover's actual covering witness.
  let C := S.affineOpenCover
  let i := C.idx s
  let R : CommRingCat.{u} := C.X i
  let j : Spec R ⟶ S := C.f i
  letI : IsOpenImmersion j := C.map_prop i
  obtain ⟨p, hp⟩ := (show ∃ p : Spec R, j p = s from C.covers s)
  letI : p.asIdeal.IsPrime := p.isPrime

  -- Both directions come from point transport and the two native residue isos.
  let baseIso : S.residueField s ≅ CommRingCat.of p.asIdeal.ResidueField :=
    (S.residueFieldCongr hp).symm ≪≫ asIso (j.residueFieldMap p) ≪≫
      Scheme.Spec.residueFieldIso R p
  let e : S.residueField s ≃+* p.asIdeal.ResidueField :=
    baseIso.commRingCatIsoToRingEquiv

  -- Retain the original κ(s)-algebra on k, and pull it back only along e.symm.
  letI : Algebra p.asIdeal.ResidueField k := Algebra.compHom k e.symm.toRingHom
  have he : (algebraMap p.asIdeal.ResidueField k).comp e.toRingHom =
      (RingEquiv.refl k).toRingHom.comp (algebraMap (S.residueField s) k) := by
    ext a
    change algebraMap (S.residueField s) k (e.symm (e a)) =
      algebraMap (S.residueField s) k a
    exact congrArg (algebraMap (S.residueField s) k) (e.symm_apply_apply a)
  letI : Module.Finite p.asIdeal.ResidueField k :=
    Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he
  letI : Algebra.IsSeparable p.asIdeal.ResidueField k :=
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he

  -- The accepted ring-level provider supplies the actual pointed étale algebra.
  obtain ⟨E, hF⟩ := PrimeSpectrum.EtalePoint.exists_with_residueFieldEquiv p k
  letI : E.point.asIdeal.IsPrime := E.point.isPrime
  letI : Algebra p.asIdeal.ResidueField E.point.asIdeal.ResidueField :=
    E.residueFieldAlgebra
  obtain ⟨F⟩ := hF
  let B : CommRingCat.{u} := CommRingCat.of E.carrier
  let q : Spec B := E.point
  let f : Spec B ⟶ Spec R :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R E.carrier))
  have hfpoint : f q = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R E.carrier) E.point.asIdeal = p.asIdeal
    exact E.over.symm
  letI : AlgebraicGeometry.Etale f :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)
      (φ := CommRingCat.ofHom (algebraMap R E.carrier))).2
        ((RingHom.etale_algebraMap (R := R) (S := E.carrier)).2 E.etale)
  let g : Spec B ⟶ S := f ≫ j
  letI : AlgebraicGeometry.Etale g := AlgebraicGeometry.Etale.etale_comp f j
  have hpoint : g q = s := by
    change j (f q) = s
    exact (congrArg j hfpoint).trans hp
  let N : EtaleNeighborhood S s :=
    EtaleNeighborhood.of (Scheme.Etale.mk g) q hpoint

  -- No inverse is chosen: compose the native Spec residue iso with F itself.
  let σ : N.toEtale.left.residueField N.point ≃+* E.point.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso B q).commRingCatIsoToRingEquiv
  let φ : N.toEtale.left.residueField N.point ≃+* k := σ.trans F.toRingEquiv
  -- This square uses the unchanged canonical neighborhood algebra on the left
  -- and E.residueFieldAlgebra on the right. Only its naturality law is pending.
  have hbase : ∀ a : S.residueField s,
      σ (algebraMap (S.residueField s) (N.toEtale.left.residueField N.point) a) =
        algebraMap p.asIdeal.ResidueField E.point.asIdeal.ResidueField (e a) := by
    sorry
  have hφ : ∀ a : S.residueField s,
      φ (algebraMap (S.residueField s) (N.toEtale.left.residueField N.point) a) =
        algebraMap (S.residueField s) k a := by
    intro a
    change F (σ (algebraMap (S.residueField s)
      (N.toEtale.left.residueField N.point) a)) = algebraMap (S.residueField s) k a
    rw [hbase a, F.commutes]
    change algebraMap (S.residueField s) k (e.symm (e a)) =
      algebraMap (S.residueField s) k a
    exact congrArg (algebraMap (S.residueField s) k) (e.symm_apply_apply a)
  let equiv : N.toEtale.left.residueField N.point ≃ₐ[S.residueField s] k :=
    AlgEquiv.ofRingEquiv (f := φ) hφ
  exact ⟨N, ⟨equiv⟩⟩

end AlgebraicGeometry.Scheme.EtaleNeighborhood
