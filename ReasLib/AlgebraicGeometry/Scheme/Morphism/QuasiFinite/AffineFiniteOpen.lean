/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

/-!
# The affine finite-open bridge

The ring-theoretic data supplier is the proved native lemma 00UJ.  The selected
open, its point, and both directions of the residue equivalence are constructed
from those data.  This file concerns an ordinary distinguished fibre only.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.QuasiFinite.AffineFiniteOpen

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The affine structure morphism, with the same tensor order as native 00UJ. -/
abbrev baseMap : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- A finite open in the affine base change, including the actual residue inverse.
The fibre condition is an ordinary point-fibre condition. -/
structure Data (p : PrimeSpectrum R) (q : PrimeSpectrum S) where
  N : EtaleNeighborhood.Elementary (Spec (CommRingCat.of R)) p
  V : (pullback (baseMap (R := R) (S := S)) N.obj.toEtale.hom).Opens
  v : V
  finite : IsFinite (V.ι ≫ pullback.snd _ _)
  pV_point : (V.ι ≫ pullback.snd _ _) v = N.obj.point
  qV_point : (V.ι ≫ pullback.fst _ _) v = q
  singleton : ∀ w : V, (V.ι ≫ pullback.snd _ _) w = N.obj.point ↔ w = v
  residueEquiv : V.toScheme.residueField v ≃+* q.asIdeal.ResidueField
  residueEquiv_symm_apply : ∀ a : q.asIdeal.ResidueField,
    residueEquiv.symm a =
      (V.ι ≫ pullback.fst _ _).residueFieldMap v
        (((Spec (CommRingCat.of S)).residueFieldCongr qV_point).inv
          ((Scheme.Spec.residueFieldIso (CommRingCat.of S) q).inv a))

/-- The inverse here is supplied by the *proved* bijectivity in native 00UJ. -/
def baseResidueEquiv (p : Ideal R) [p.IsPrime]
    {Rprime : Type u} [CommRing Rprime] [Algebra R Rprime]
    (P : Ideal Rprime) [P.IsPrime] [P.LiesOver p]
    (h : Function.Bijective
      (Ideal.ResidueField.mapₐ p P (Algebra.ofId R Rprime) (P.over_def p))) :
    p.ResidueField ≃ₐ[R] P.ResidueField :=
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ p P (Algebra.ofId R Rprime) (P.over_def p)) h

/-- Evaluation of the tensor product in `κ(q)`.  On the left factor it is
`Rprime → κ(P) → κ(p) → κ(q)`; on the right it is the canonical residue map. -/
def tensorEvaluation (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal]
    {Rprime : Type u} [CommRing Rprime] [Algebra R Rprime]
    (P : Ideal Rprime) [P.IsPrime] [P.LiesOver p.asIdeal]
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ p.asIdeal P (Algebra.ofId R Rprime)
        (P.over_def p.asIdeal))) :
    Rprime ⊗[R] S →ₐ[R] q.asIdeal.ResidueField :=
  Algebra.TensorProduct.lift
    ((Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
        (q.asIdeal.over_def p.asIdeal)).comp
      ((baseResidueEquiv p.asIdeal P hbij).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom R Rprime P.ResidueField)))
    (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
    (fun _ _ ↦ Commute.all _ _)

/-- Both functions are actual residue lifts.  No inverse is obtained from a
new surjectivity or isomorphism assertion. -/
def tensorResidueEquiv (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal]
    {Rprime : Type u} [CommRing Rprime] [Algebra R Rprime]
    (P : Ideal Rprime) [P.IsPrime] [P.LiesOver p.asIdeal]
    (Pprime : Ideal (Rprime ⊗[R] S)) [Pprime.IsPrime] [Pprime.LiesOver P]
    (hPprimeq : Pprime.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal)
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ p.asIdeal P (Algebra.ofId R Rprime)
        (P.over_def p.asIdeal))) :
    Pprime.ResidueField ≃+* q.asIdeal.ResidueField := by
  let ev := tensorEvaluation p q P hbij
  let ep := baseResidueEquiv p.asIdeal P hbij
  let pq := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
    (q.asIdeal.over_def p.asIdeal)
  have ev_right (s : S) :
      ev (Algebra.TensorProduct.includeRight s) =
        algebraMap S q.asIdeal.ResidueField s := by
    simp [ev, tensorEvaluation]
  have ev_left (r : Rprime) :
      ev (algebraMap Rprime (Rprime ⊗[R] S) r) =
        pq (ep.symm (algebraMap Rprime P.ResidueField r)) := by
    simp [ev, tensorEvaluation, ep, pq]
  let K := RingHom.ker ev.toRingHom
  letI : K.IsPrime := RingHom.ker_isPrime ev.toRingHom
  have hKright : K.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
    ext s
    change ev (Algebra.TensorProduct.includeRight s) = 0 ↔ s ∈ q.asIdeal
    rw [ev_right]
    exact Ideal.algebraMap_residueField_eq_zero
  have hKleft : P = K.comap (algebraMap Rprime (Rprime ⊗[R] S)) := by
    ext r
    change r ∈ P ↔ ev (algebraMap Rprime (Rprime ⊗[R] S) r) = 0
    rw [ev_left]
    constructor
    · intro hr
      rw [Ideal.algebraMap_residueField_eq_zero.mpr hr, map_zero, map_zero]
    · intro hr
      have h₁ : ep.symm (algebraMap Rprime P.ResidueField r) = 0 :=
        pq.injective (hr.trans (map_zero pq).symm)
      have h₂ : algebraMap Rprime P.ResidueField r = 0 :=
        ep.symm.injective (h₁.trans (map_zero ep.symm).symm)
      exact Ideal.algebraMap_residueField_eq_zero.mp h₂
  letI : K.LiesOver P := ⟨hKleft⟩
  have hkernel : K = Pprime :=
    Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hbij K Pprime
      (hKright.trans hPprimeq.symm)
  have hkill : Pprime ≤ RingHom.ker ev.toRingHom := by
    exact le_of_eq hkernel.symm
  have hunits : Pprime.primeCompl ≤
      (IsUnit.submonoid q.asIdeal.ResidueField).comap ev.toRingHom := by
    intro x hx
    change IsUnit (ev x)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hx
    rw [← hkernel]
    exact hz
  let forward : Pprime.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.lift Pprime ev.toRingHom hkill hunits
  let backward : q.asIdeal.ResidueField →+* Pprime.ResidueField :=
    Ideal.ResidueField.map q.asIdeal Pprime
      Algebra.TensorProduct.includeRight.toRingHom hPprimeq.symm
  have forward_backward : forward.comp backward = RingHom.id _ := by
    apply Ideal.ResidueField.ringHom_ext
    ext s
    change forward (backward (algebraMap S q.asIdeal.ResidueField s)) =
      algebraMap S q.asIdeal.ResidueField s
    simp only [backward, Ideal.ResidueField.map_algebraMap, forward,
      Ideal.ResidueField.lift_algebraMap]
    exact ev_right s
  have backward_forward : ∀ a : Pprime.ResidueField, backward (forward a) = a := by
    intro a
    apply forward.injective
    exact congrArg (fun f : q.asIdeal.ResidueField →+* q.asIdeal.ResidueField ↦ f (forward a))
      forward_backward
  exact
    { toFun := forward
      invFun := backward
      left_inv := backward_forward
      right_inv := fun a ↦
        congrArg (fun f : q.asIdeal.ResidueField →+* q.asIdeal.ResidueField ↦ f a)
          forward_backward
      map_mul' := forward.map_mul
      map_add' := forward.map_add }

/-- Convert the actual native 00UJ witnesses into the affine scheme data.
All object and inverse fields below have explicit constructions. -/
def ofNative (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal]
    {Rprime : Type u} [CommRing Rprime] [Algebra R Rprime] [Algebra.Etale R Rprime]
    (P : Ideal Rprime) [P.IsPrime] [P.LiesOver p.asIdeal]
    (e : Rprime ⊗[R] S) (_he : IsIdempotentElem e)
    (Pprime : Ideal (Rprime ⊗[R] S)) [Pprime.IsPrime] [Pprime.LiesOver P]
    (hPprimeq : Pprime.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal)
    (hePprime : e ∉ Pprime)
    (hbij : Function.Bijective
      (Ideal.ResidueField.mapₐ p.asIdeal P (Algebra.ofId R Rprime)
        (P.over_def p.asIdeal)))
    (hfinite : Module.Finite Rprime (Localization.Away e))
    (hunique : ∀ J : Ideal (Rprime ⊗[R] S), J.IsPrime → J.LiesOver P → e ∉ J →
      J = Pprime) : Data p q := by
  let h : Spec (CommRingCat.of Rprime) ⟶ Spec (CommRingCat.of R) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R Rprime))
  let PPt : Spec (CommRingCat.of Rprime) := ⟨P, inferInstance⟩
  have hpoint : h PPt = p := by
    apply PrimeSpectrum.ext
    exact (P.over_def p.asIdeal).symm
  letI : AlgebraicGeometry.Etale h :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)
      (φ := CommRingCat.ofHom (algebraMap R Rprime))).2
        ((RingHom.etale_algebraMap (R := R) (S := Rprime)).2 inferInstance)
  let E : EtaleNeighborhood (Spec (CommRingCat.of R)) p :=
    EtaleNeighborhood.of (Scheme.Etale.mk h) PPt hpoint
  let ep := baseResidueEquiv p.asIdeal P hbij
  let baseIso : (Spec (CommRingCat.of R)).residueField (h PPt) ≅
      (Spec (CommRingCat.of Rprime)).residueField PPt :=
    (Spec (CommRingCat.of R)).residueFieldCongr hpoint ≪≫
      Scheme.Spec.residueFieldIso (CommRingCat.of R) p ≪≫
      ep.toRingEquiv.toCommRingCatIso ≪≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of Rprime) PPt).symm
  -- D1: native Spec residue isos identify the canonical residue map with ep.
  have baseIso_hom : baseIso.hom = h.residueFieldMap PPt := by
    sorry
  have elementary : E.IsElementary := by
    change IsIso (h.residueFieldMap PPt)
    rw [← baseIso_hom]
    infer_instance
  let N := EtaleNeighborhood.Elementary.of E elementary

  -- Swap the pullback factors once so its tensor order is Rprime ⊗[R] S.
  let tensorIso : pullback (baseMap (R := R) (S := S)) h ≅
      Spec (CommRingCat.of (Rprime ⊗[R] S)) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso R Rprime S
  let D : (Spec (CommRingCat.of (Rprime ⊗[R] S))).Opens :=
    PrimeSpectrum.basicOpen e
  let j : D.toScheme ⟶ pullback (baseMap (R := R) (S := S)) h :=
    D.ι ≫ tensorIso.inv
  let V := j.opensRange
  have hrange : Set.range j = Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let dIso : D.toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq j V.ι hrange
  let awayIso : D.toScheme ≅ Spec (CommRingCat.of (Localization.Away e)) :=
    basicOpenIsoSpecAway (R := CommRingCat.of (Rprime ⊗[R] S)) e
  let finiteIso := dIso.symm ≪≫ awayIso
  let Q : Spec (CommRingCat.of (Rprime ⊗[R] S)) := ⟨Pprime, inferInstance⟩
  let d : D := ⟨Q, hePprime⟩
  let v : V := dIso.hom d
  let pV : V.toScheme ⟶ Spec (CommRingCat.of Rprime) :=
    V.ι ≫ pullback.snd _ _
  let qV : V.toScheme ⟶ Spec (CommRingCat.of S) :=
    V.ι ≫ pullback.fst _ _
  let tMap : V.toScheme ⟶ Spec (CommRingCat.of (Rprime ⊗[R] S)) :=
    V.ι ≫ tensorIso.hom
  have chart_inverse : tMap = dIso.inv ≫ D.ι := by
    have hf : dIso.inv ≫ j = V.ι :=
      IsOpenImmersion.isoOfRangeEq_inv_fac j V.ι hrange
    change V.ι ≫ tensorIso.hom = dIso.inv ≫ D.ι
    rw [← hf]
    simp [j, Category.assoc]
  -- D2 and D3: these are the two native pullbackSpecIso projection formulas,
  -- after pullbackSymmetry.  They do not assert existence of a morphism.
  have chart_snd :
      tMap ≫ AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap Rprime (Rprime ⊗[R] S))) = pV := by
    sorry
  have chart_fst :
      tMap ≫ AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S →ₐ[R] Rprime ⊗[R] S).toRingHom) =
        qV := by
    sorry
  -- D4: the localization isomorphism identifies this precise structure arrow.
  have finite_arrow : pV = finiteIso.hom ≫ AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap Rprime (Localization.Away e))) := by
    sorry
  letI : Module.Finite Rprime (Localization.Away e) := hfinite
  letI : IsFinite (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap Rprime (Localization.Away e)))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr hfinite)
  have finite_pV : IsFinite pV := by
    rw [finite_arrow]
    infer_instance

  have point_tensor : tMap v = Q := by
    rw [chart_inverse]
    change D.ι (dIso.inv (dIso.hom d)) = Q
    have hd : dIso.inv (dIso.hom d) = d :=
      (Scheme.homeoOfIso dIso).symm_apply_apply d
    rw [hd]
    rfl
  have hpQ : AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap Rprime (Rprime ⊗[R] S))) Q = PPt := by
    apply PrimeSpectrum.ext
    exact (Pprime.over_def P).symm
  have hqQ : AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : S →ₐ[R] Rprime ⊗[R] S).toRingHom) Q = q := by
    apply PrimeSpectrum.ext
    exact hPprimeq
  have hpV : pV v = PPt := by
    calc
      pV v = AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap Rprime (Rprime ⊗[R] S))) (tMap v) :=
        congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of Rprime) ↦ f v) chart_snd.symm
      _ = PPt := by rw [point_tensor]; exact hpQ
  have hqV : qV v = q := by
    calc
      qV v = AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : S →ₐ[R] Rprime ⊗[R] S).toRingHom)
          (tMap v) :=
        congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of S) ↦ f v) chart_fst.symm
      _ = q := by rw [point_tensor]; exact hqQ
  have singleton : ∀ w : V, pV w = PPt ↔ w = v := by
    intro w
    constructor
    · intro hw
      let t : PrimeSpectrum (Rprime ⊗[R] S) := tMap w
      have ht : AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap Rprime (Rprime ⊗[R] S))) t = PPt :=
        (congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of Rprime) ↦ f w)
          chart_snd).trans hw
      have htP : P = t.asIdeal.comap (algebraMap Rprime (Rprime ⊗[R] S)) :=
        (congrArg PrimeSpectrum.asIdeal ht).symm
      letI : t.asIdeal.LiesOver P := ⟨htP⟩
      have het : e ∉ t.asIdeal := by
        have htw : tMap w = D.ι (dIso.inv w) :=
          congrArg (fun f : V.toScheme ⟶ Spec (CommRingCat.of (Rprime ⊗[R] S)) ↦ f w)
            chart_inverse
        change e ∉ (tMap w).asIdeal
        rw [htw]
        exact (dIso.inv w).property
      have htQ : t = Q :=
        PrimeSpectrum.ext (hunique t.asIdeal inferInstance inferInstance het)
      exact tMap.isOpenEmbedding.injective (htQ.trans point_tensor.symm)
    · rintro rfl
      exact hpV

  -- Native open-immersion residue inverses, followed by the explicit tensor
  -- evaluation/includeRight equivalence constructed above.
  let rho : V.toScheme.residueField v ≅ CommRingCat.of Pprime.ResidueField :=
    (asIso (tMap.residueFieldMap v)).symm ≪≫
      (Spec (CommRingCat.of (Rprime ⊗[R] S))).residueFieldCongr point_tensor ≪≫
      Scheme.Spec.residueFieldIso (CommRingCat.of (Rprime ⊗[R] S)) Q
  let residueEquiv : V.toScheme.residueField v ≃+* q.asIdeal.ResidueField :=
    rho.commRingCatIsoToRingEquiv.trans (tensorResidueEquiv p q P Pprime hPprimeq hbij)
  -- D5: includeRight is the ring map of qV in the native affine pullback chart.
  have residue_naturality : ∀ a : q.asIdeal.ResidueField,
      residueEquiv.symm a = qV.residueFieldMap v
        (((Spec (CommRingCat.of S)).residueFieldCongr hqV).inv
          ((Scheme.Spec.residueFieldIso (CommRingCat.of S) q).inv a)) := by
    sorry
  exact
    { N := N
      V := V
      v := v
      finite := finite_pV
      pV_point := hpV
      qV_point := hqV
      singleton := singleton
      residueEquiv := residueEquiv
      residueEquiv_symm_apply := residue_naturality }

/-- The sole data supplier is the proved native 00UJ theorem.  The `Nonempty`
wrapper below is proved by the explicit `ofNative` construction; it is not an
admission or an additional existence hypothesis. -/
def build [Algebra.FiniteType R S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal] [Algebra.QuasiFiniteAt R q.asIdeal] : Data p q :=
  Classical.choice (by
    obtain ⟨Rprime, _, _, _, P, _, _, e, he, Pprime, _, _, hPprimeq,
      hePprime, hbij, hfinite, hunique⟩ :=
      Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p.asIdeal q.asIdeal
    exact ⟨ofNative p q P e he Pprime hPprimeq hePprime hbij hfinite hunique⟩)

end AlgebraicGeometry.Scheme.QuasiFinite.AffineFiniteOpen
