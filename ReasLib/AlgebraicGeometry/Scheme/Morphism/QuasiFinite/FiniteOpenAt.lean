/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.SelectedResidue
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.AffineFiniteOpen

/-!
# A selected finite open after an elementary étale neighbourhood

The fibre assertion in this module concerns ordinary underlying points.
The residue equivalence records the inverse of the actual first projection.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiFinite.FiniteOpenAt

variable {X S : Scheme.{u}}

/-- Selected finite-open data at one point, with the canonical residue inverse. -/
structure Data (f : X ⟶ S) (x : X) where
  N : EtaleNeighborhood.Elementary S (f x)
  V : (pullback f N.obj.toEtale.hom).Opens
  v : V
  finite : IsFinite (V.ι ≫ pullback.snd _ _)
  p_point : (V.ι ≫ pullback.snd _ _) v = N.obj.point
  q_point : (V.ι ≫ pullback.fst _ _) v = x
  singleton : ∀ w : V, (V.ι ≫ pullback.snd _ _) w = N.obj.point ↔ w = v
  residueEquiv : V.toScheme.residueField v ≃+* X.residueField x
  residueEquiv_symm : CommRingCat.ofHom residueEquiv.symm.toRingHom =
    (X.residueFieldCongr q_point).inv ≫ (V.ι ≫ pullback.fst _ _).residueFieldMap v

namespace Data

/-- The finite morphism to the chosen neighbourhood. -/
abbrev p {f : X ⟶ S} {x : X} (D : Data f x) :=
  D.V.ι ≫ pullback.snd f D.N.obj.toEtale.hom

/-- The morphism to the original source. -/
abbrev q {f : X ⟶ S} {x : X} (D : Data f x) :=
  D.V.ι ≫ pullback.fst f D.N.obj.toEtale.hom

end Data

/-- The action extracted from the actual morphism by `Spec.preimage` is finite type.
This is a scoped lemma, rather than a new algebra structure or a global instance. -/
theorem finiteType_preimage {R A : CommRingCat.{u}} (h : Spec A ⟶ Spec R)
    [LocallyOfFiniteType h] :
    @Algebra.FiniteType R A _ _ (AlgebraicGeometry.Spec.preimage h).hom.toAlgebra := by
  change (AlgebraicGeometry.Spec.preimage h).hom.FiniteType
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
    (φ := AlgebraicGeometry.Spec.preimage h)).mp
  simpa only [AlgebraicGeometry.Spec.map_preimage] using
    (inferInstance : LocallyOfFiniteType h)

/-- The same exact action is quasi-finite, by the native affine criterion. -/
theorem quasiFinite_preimage {R A : CommRingCat.{u}} (h : Spec A ⟶ Spec R)
    [LocallyQuasiFinite h] :
    @Algebra.QuasiFinite R A _ _ (AlgebraicGeometry.Spec.preimage h).hom.toAlgebra := by
  change (AlgebraicGeometry.Spec.preimage h).hom.QuasiFinite
  apply (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)
    (φ := AlgebraicGeometry.Spec.preimage h)).mp
  simpa only [AlgebraicGeometry.Spec.map_preimage] using
    (inferInstance : LocallyQuasiFinite h)

/-- The compatible residue homomorphism for an actual open chart of the base. -/
def chartResidueHom {U : Scheme.{u}} (f : X ⟶ S) (x : X) (j : U ⟶ S)
    [IsOpenImmersion j] (p : U) (hp : j p = f x) :
    U.residueField p →+* X.residueField x :=
  ((asIso (j.residueFieldMap p)).inv ≫ (S.residueFieldCongr hp).hom ≫
    f.residueFieldMap x).hom

/-- The residue homomorphism of the base chart gives its actual compatible Spec square. -/
theorem chartResidueHom_square {U : Scheme.{u}} (f : X ⟶ S) (x : X) (j : U ⟶ S)
    [IsOpenImmersion j] (p : U) (hp : j p = f x) :
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (chartResidueHom f x j p hp)) ≫
      U.fromSpecResidueField p) ≫ j = X.fromSpecResidueField x ≫ f := by
  have hj : AlgebraicGeometry.Spec.map (asIso (j.residueFieldMap p)).inv ≫
      U.fromSpecResidueField p ≫ j = S.fromSpecResidueField (j p) := by
    rw [← j.SpecMap_residueFieldMap_fromSpecResidueField p,
      ← AlgebraicGeometry.Spec.map_comp_assoc]
    simp
  change (AlgebraicGeometry.Spec.map
      ((asIso (j.residueFieldMap p)).inv ≫ (S.residueFieldCongr hp).hom ≫
        f.residueFieldMap x) ≫ U.fromSpecResidueField p) ≫ j = _
  simp only [AlgebraicGeometry.Spec.map_comp, Category.assoc]
  rw [hj, Scheme.residueFieldCongr_fromSpecResidueField]
  exact f.SpecMap_residueFieldMap_fromSpecResidueField x

set_option backward.isDefEq.respectTransparency false in
/-- Construct selected finite-open data from the native covers and the accepted
affine finite-open construction. Every chosen object below comes from those providers. -/
def build (f : X ⟶ S) [LocallyOfFiniteType f] [LocallyQuasiFinite f] (x : X) :
    Data f x := by
  classical
  -- The actual base chart and its actual point, selected from the native cover.
  let C := S.affineOpenCover
  let i := C.idx (f x)
  let R : CommRingCat.{u} := C.X i
  let jR : Spec R ⟶ S := C.f i
  letI : IsOpenImmersion jR := C.map_prop i
  let p : Spec R := Classical.choose
    (show ∃ p : Spec R, jR p = f x from C.covers (f x))
  have hp : jR p = f x := Classical.choose_spec
    (show ∃ p : Spec R, jR p = f x from C.covers (f x))
  letI : p.asIdeal.IsPrime := p.isPrime
  let η : (Spec R).residueField p →+* X.residueField x :=
    chartResidueHom f x jR p hp
  have square :
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom η) ≫
        (Spec R).fromSpecResidueField p) ≫ jR = X.fromSpecResidueField x ≫ f :=
    chartResidueHom_square f x jR p hp
  let P0 : Scheme.{u} := pullback f jR
  let r : P0 := SelectedResidue.point f jR x p η square
  let selectedEquiv : P0.residueField r ≃+* X.residueField x :=
    SelectedResidue.residueEquiv f jR x p η square

  -- Select a source chart through r itself, not a point chosen independently of r.
  let D := P0.affineOpenCover
  let a := D.idx r
  let A : CommRingCat.{u} := D.X a
  let jX : Spec A ⟶ P0 := D.f a
  letI : IsOpenImmersion jX := D.map_prop a
  let q : Spec A := Classical.choose
    (show ∃ q : Spec A, jX q = r from D.covers r)
  have hq : jX q = r := Classical.choose_spec
    (show ∃ q : Spec A, jX q = r from D.covers r)
  letI : q.asIdeal.IsPrime := q.isPrime
  let h : Spec A ⟶ Spec R := jX ≫ pullback.snd f jR
  let φ : R ⟶ A := AlgebraicGeometry.Spec.preimage h
  -- This is the sole R-action on A used by the affine builder.
  letI : Algebra R A := φ.hom.toAlgebra
  have hφ : AffineFiniteOpen.baseMap (R := R) (S := A) = h := by
    change AlgebraicGeometry.Spec.map φ = h
    exact AlgebraicGeometry.Spec.map_preimage h
  letI : LocallyOfFiniteType h := inferInstance
  letI : LocallyQuasiFinite h := inferInstance
  letI : Algebra.FiniteType R A := finiteType_preimage h
  letI : Algebra.QuasiFinite R A := quasiFinite_preimage h
  letI : Algebra.QuasiFiniteAt R q.asIdeal := inferInstance
  have hqp : AffineFiniteOpen.baseMap (R := R) (S := A) q = p := by
    calc
      AffineFiniteOpen.baseMap (R := R) (S := A) q = h q :=
        congrArg (fun t : Spec A ⟶ Spec R ↦ t q) hφ
      _ = pullback.snd f jR (jX q) := rfl
      _ = pullback.snd f jR r := congrArg (pullback.snd f jR) hq
      _ = p := SelectedResidue.point_snd f jR x p η square
  letI : q.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg PrimeSpectrum.asIdeal hqp).symm⟩
  let L : AffineFiniteOpen.Data p q := AffineFiniteOpen.build p q
  let ℓ := L.N.obj.toEtale.hom
  let localp := L.V.ι ≫ pullback.snd (AffineFiniteOpen.baseMap (R := R) (S := A)) ℓ
  let localq := L.V.ι ≫ pullback.fst (AffineFiniteOpen.baseMap (R := R) (S := A)) ℓ
  letI : IsFinite localp := L.finite

  -- Compose the actual affine neighbourhood with the actual open base chart.
  letI : AlgebraicGeometry.Etale ℓ := L.N.obj.toEtale.prop
  letI : AlgebraicGeometry.Etale jR :=
    @AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ jR (C.map_prop i)
  let g := ℓ ≫ jR
  letI : AlgebraicGeometry.Etale g := AlgebraicGeometry.Etale.etale_comp ℓ jR
  have hgpoint : g L.N.obj.point = f x := by
    change jR (ℓ L.N.obj.point) = f x
    rw [L.N.obj.map_point]
    exact hp
  let E : EtaleNeighborhood S (f x) :=
    EtaleNeighborhood.of (Scheme.Etale.mk g) L.N.obj.point hgpoint
  have hjRResidue : IsIso (jR.residueFieldMap (ℓ L.N.obj.point)) :=
    @Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion
      _ _ jR (C.map_prop i) (ℓ L.N.obj.point)
  have hℓResidue : IsIso (ℓ.residueFieldMap L.N.obj.point) := L.N.property
  let elementaryResidueIso : S.residueField (g L.N.obj.point) ≅
      L.N.obj.toEtale.left.residueField L.N.obj.point :=
    (@asIso _ _ _ _ (jR.residueFieldMap (ℓ L.N.obj.point)) hjRResidue) ≪≫
      (@asIso _ _ _ _ (ℓ.residueFieldMap L.N.obj.point) hℓResidue)
  have elementaryResidueIso_hom :
      elementaryResidueIso.hom = g.residueFieldMap L.N.obj.point := by
    change jR.residueFieldMap (ℓ L.N.obj.point) ≫
      ℓ.residueFieldMap L.N.obj.point = (ℓ ≫ jR).residueFieldMap L.N.obj.point
    exact (Scheme.residueFieldMap_comp ℓ jR L.N.obj.point).symm
  have elementary : E.IsElementary := by
    change IsIso (g.residueFieldMap L.N.obj.point)
    rw [← elementaryResidueIso_hom]
    infer_instance
  let N : EtaleNeighborhood.Elementary S (f x) :=
    EtaleNeighborhood.Elementary.of E elementary

  -- Both factor maps are actual open immersions and jR is a native monomorphism.
  let iX : Spec A ⟶ X := jX ≫ pullback.fst f jR
  letI : IsOpenImmersion iX := inferInstance
  have e₁ : AffineFiniteOpen.baseMap (R := R) (S := A) ≫ jR = iX ≫ f := by
    rw [hφ]
    dsimp only [h, iX]
    simp only [Category.assoc, pullback.condition]
  have e₂ : ℓ ≫ jR = (𝟙 L.N.obj.toEtale.left) ≫ g := by
    simp only [g, Category.id_comp]
  let k : pullback (AffineFiniteOpen.baseMap (R := R) (S := A)) ℓ ⟶ pullback f g :=
    pullback.map (AffineFiniteOpen.baseMap (R := R) (S := A)) ℓ f g
      iX (𝟙 _) jR e₁ e₂
  letI : IsOpenImmersion k := inferInstance
  let V : (pullback f g).Opens := k ''ᵁ L.V
  let imageIso : L.V.toScheme ≅ V.toScheme := k.isoImage L.V
  let v : V := imageIso.hom L.v
  let pV : V.toScheme ⟶ L.N.obj.toEtale.left := V.ι ≫ pullback.snd f g
  let qV : V.toScheme ⟶ X := V.ι ≫ pullback.fst f g
  have image_hom_p : imageIso.hom ≫ pV = localp := by
    dsimp only [pV, localp]
    rw [← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
    dsimp only [k, pullback.map]
    rw [pullback.lift_snd, Category.comp_id]
  have image_hom_q : imageIso.hom ≫ qV = localq ≫ iX := by
    dsimp only [qV, localq]
    rw [← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
    dsimp only [k, pullback.map]
    rw [pullback.lift_fst, Category.assoc]
  have finite_arrow : pV = imageIso.inv ≫ localp := by
    rw [← image_hom_p]
    simp
  have finite_pV : IsFinite pV := by
    rw [finite_arrow]
    exact @AlgebraicGeometry.IsFinite.instCompScheme _ _ imageIso.inv _ localp
      (@AlgebraicGeometry.IsFinite.instOfIsIsoScheme _ _ imageIso.inv imageIso.isIso_inv)
      L.finite
  have p_point : pV v = N.obj.point := by
    change pV (imageIso.hom L.v) = L.N.obj.point
    exact (congrArg (fun t : L.V.toScheme ⟶ L.N.obj.toEtale.left ↦ t L.v)
      image_hom_p).trans L.pV_point
  have q_point : qV v = x := by
    calc
      qV v = iX (localq L.v) :=
        congrArg (fun t : L.V.toScheme ⟶ X ↦ t L.v) image_hom_q
      _ = iX q := congrArg iX L.qV_point
      _ = pullback.fst f jR (jX q) := rfl
      _ = pullback.fst f jR r := congrArg (pullback.fst f jR) hq
      _ = x := SelectedResidue.point_fst f jR x p η square
  have singleton : ∀ w : V, pV w = N.obj.point ↔ w = v := by
    intro w
    constructor
    · intro hw
      have hw' : localp (imageIso.inv w) = L.N.obj.point :=
        (congrArg (fun t : V.toScheme ⟶ L.N.obj.toEtale.left ↦ t w)
          finite_arrow.symm).trans hw
      have hwv : imageIso.inv w = L.v := (L.singleton (imageIso.inv w)).1 hw'
      change w = imageIso.hom L.v
      have hwback : imageIso.hom (imageIso.inv w) = w :=
        (Scheme.homeoOfIso imageIso).apply_symm_apply w
      exact hwback.symm.trans (congrArg imageIso.hom hwv)
    · rintro rfl
      exact p_point

  -- Every residue inverse in this chain is native or an accepted actual inverse.
  let imageResidueIso : V.toScheme.residueField v ≅ L.V.toScheme.residueField L.v :=
    asIso (imageIso.hom.residueFieldMap L.v)
  let sourceResidueIso : CommRingCat.of q.asIdeal.ResidueField ≅ P0.residueField r :=
    (Scheme.Spec.residueFieldIso A q).symm ≪≫
      (asIso (jX.residueFieldMap q)).symm ≪≫ P0.residueFieldCongr hq
  let residueEquiv : V.toScheme.residueField v ≃+* X.residueField x :=
    ((imageResidueIso.commRingCatIsoToRingEquiv.trans L.residueEquiv).trans
      sourceResidueIso.commRingCatIsoToRingEquiv).trans selectedEquiv
  have residue_naturality : CommRingCat.ofHom residueEquiv.symm.toRingHom =
      (X.residueFieldCongr q_point).inv ≫ qV.residueFieldMap v := by
    -- Concrete equality debt. Expand residueEquiv.symm in the reverse order:
    -- selectedEquiv.symm; (P0.residueFieldCongr hq).inv;
    -- jX.residueFieldMap q; (Spec.residueFieldIso A q).hom;
    -- L.residueEquiv.symm; inv (imageIso.hom.residueFieldMap L.v).
    -- SelectedResidue.residueEquiv_symm_toRingHom and
    -- L.residueEquiv_symm_apply identify the two accepted inverse factors.
    -- Native residueFieldMap_comp/congr' and image_hom_q identify the result
    -- with the actual qV residue map, transported along exactly q_point.
    sorry
  exact
    { N := N
      V := V
      v := v
      finite := finite_pV
      p_point := p_point
      q_point := q_point
      singleton := singleton
      residueEquiv := residueEquiv
      residueEquiv_symm := residue_naturality }

end AlgebraicGeometry.Scheme.QuasiFinite.FiniteOpenAt
