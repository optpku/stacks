/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.FirstRow
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective

/-!
# The general linear scheme of rank two

Coordinates are indexed by matrix positions, rather than an unrelated four-element type. The
first row gives explicit compatible morphisms to the affine plane, punctured affine plane, and
projective line.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

universe u

namespace GLTwo

section CommRing

variable (k : Type u) [CommRing k]

/-- The universe-lifted matrix index used by the relative affine-space model of `GL₂`. -/
@[stacks 01KX "rank-two matrix index"]
abbrev index : Type u := ULift.{u} (Fin 2)

/-- The polynomial coordinate ring `k[a,b,c,d]`, indexed by positions of a `2 × 2` matrix. -/
@[stacks 01KX "rank-two polynomial coordinate ring"]
abbrev polynomialRing : Type u := GeneralLinear.polynomialRing k (index)

/-- The upper-left matrix coordinate `a`. -/
@[stacks 01KX "rank-two matrix coordinate a"]
abbrev a : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 0) (ULift.up 0)

/-- The upper-right matrix coordinate `b`. -/
@[stacks 01KX "rank-two matrix coordinate b"]
abbrev b : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 0) (ULift.up 1)

/-- The lower-left matrix coordinate `c`. -/
@[stacks 01KX "rank-two matrix coordinate c"]
abbrev c : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 1) (ULift.up 0)

/-- The lower-right matrix coordinate `d`. -/
@[stacks 01KX "rank-two matrix coordinate d"]
abbrev d : polynomialRing k :=
  GeneralLinear.coordinate k (index) (ULift.up 1) (ULift.up 1)

/-- The determinant `ad - bc` of the generic `2 × 2` matrix. -/
@[stacks 01KX "rank-two determinant"]
abbrev det : polynomialRing k := GeneralLinear.determinant k (index)

/-- In rank two, the generic determinant is `ad - bc`. -/
@[stacks 01KX "rank-two determinant formula"]
theorem det_eq_ad_sub_bc : det k = a k * d k - b k * c k := by
  change Matrix.det (GeneralLinear.genericMatrix k index) = _
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ulift : index ≃ Fin 2).symm
    (GeneralLinear.genericMatrix k index), Matrix.det_fin_two]
  rfl

/-- The coordinate ring `k[a,b,c,d,1/(ad-bc)]` of `GL₂`. -/
@[stacks 01KX "rank-two general-linear coordinate ring"]
abbrev coordinateRing : Type u := GeneralLinear.coordinateRing k (index)

/-- The localized upper-left coordinate. -/
@[stacks 01KX "rank-two localized coordinate a"]
abbrev localizedA : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 0) (ULift.up 0)

/-- The localized upper-right coordinate. -/
@[stacks 01KX "rank-two localized coordinate b"]
abbrev localizedB : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 0) (ULift.up 1)

/-- The localized lower-left coordinate. -/
@[stacks 01KX "rank-two localized coordinate c"]
abbrev localizedC : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 1) (ULift.up 0)

/-- The localized lower-right coordinate. -/
@[stacks 01KX "rank-two localized coordinate d"]
abbrev localizedD : coordinateRing k :=
  GeneralLinear.localizedCoordinate k (index) (ULift.up 1) (ULift.up 1)

/-- The image of the generic determinant in the coordinate ring of `GL₂`. -/
@[stacks 01KX "rank-two localized determinant"]
abbrev localizedDeterminant : coordinateRing k :=
  algebraMap (polynomialRing k) (coordinateRing k) (det k)

/-- In the coordinate ring of `GL₂`, the localized determinant is still `ad - bc`. -/
@[stacks 01KX "rank-two determinant formula"]
theorem localizedDeterminant_eq_ad_sub_bc :
    localizedDeterminant k = localizedA k * localizedD k - localizedB k * localizedC k := by
  change algebraMap (polynomialRing k) (coordinateRing k) (det k) = _
  rw [det_eq_ad_sub_bc, map_sub, map_mul, map_mul]

/-- The localized determinant is a unit in the coordinate ring of `GL₂`. -/
@[stacks 01KX "rank-two determinant unit"]
theorem localizedDeterminant_isUnit : IsUnit (localizedDeterminant k) := by
  exact IsLocalization.Away.algebraMap_isUnit (det k)

/-- The `k`-algebra map `k[x,y] ⟶ k[a,b,c,d,1/(ad-bc)]` sending `x` to `a` and `y` to
`b`. -/
@[stacks 01KX "first-row coordinate comap"]
abbrev toAffinePlaneComap :
    PuncturedAffinePlane.coordinateRing k →ₐ[k] coordinateRing k :=
  GeneralLinear.FirstRow.coordinateComap k 1

/-- The rank-two general linear scheme `GL₂,k`. -/
@[stacks 01KX]
abbrev scheme : Scheme.{u} := GeneralLinear.scheme k (index)

/-- The canonical structure morphism from `GL₂,k` to `Spec(k)`. -/
@[stacks 01KX "rank-two general-linear structure morphism"]
abbrev toBase : scheme k ⟶ Spec (CommRingCat.of k) :=
  GeneralLinear.toBase k (index)

/-- The morphism from `GL₂,k` to canonical affine `2`-space induced by the first matrix row. -/
@[stacks 01KX "first-row morphism to affine two-space"]
abbrev toAffinePlane : scheme k ⟶ PuncturedAffinePlane.affinePlane k :=
  GeneralLinear.FirstRow.toAffineSpace k 1

/-- The comorphism of `toAffinePlane` sends `x` to `a`. -/
@[simp, stacks 01KX "rank-two first-row x-coordinate"]
theorem toAffinePlaneComap_x :
    toAffinePlaneComap k (PuncturedAffinePlane.x k) = localizedA k := by
  exact MvPolynomial.aeval_X _ _

/-- The comorphism of `toAffinePlane` sends `y` to `b`. -/
@[simp, stacks 01KX "rank-two first-row y-coordinate"]
theorem toAffinePlaneComap_y :
    toAffinePlaneComap k (PuncturedAffinePlane.y k) = localizedB k := by
  exact MvPolynomial.aeval_X _ _

/-- The canonical morphism `GL₂,k ⟶ 𝔸²_k ∖ {0}` induced by the first matrix row. -/
@[stacks 01KX "first-row morphism to the punctured affine plane"]
abbrev toPuncturedAffinePlane :
    scheme k ⟶ (PuncturedAffinePlane.puncturedOpen k).toScheme :=
  GeneralLinear.FirstRow.toPuncturedAffineSpace k 1

/-- The punctured-affine morphism composes with the open inclusion to the affine first-row map. -/
@[reassoc (attr := simp), stacks 01KX "rank-two punctured inclusion"]
theorem toPuncturedAffinePlane_ι :
    toPuncturedAffinePlane k ≫ (PuncturedAffinePlane.puncturedOpen k).ι =
      toAffinePlane k := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- The canonical morphism from `GL₂,k` to the projective line obtained by projectivizing its
first row. -/
@[stacks 01KX]
abbrev toProjectiveLine : scheme k ⟶ ProjectiveSpace.scheme k 1 :=
  GeneralLinear.FirstRow.toProjectiveSpace k 1

open PuncturedAffineSpace in
set_option backward.isDefEq.respectTransparency false in
/-- Compute the structure map of the glued projectivization on its coordinate cover. -/
private theorem projectivization_toSpecZero (k : Type u) [CommRing k] (n : ℕ) :
    toProjectiveSpace k n ≫ Proj.toSpecZero (ProjectiveSpace.grading k n) =
      (puncturedOpen (projectiveIndex n) k).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          ((Projectivization.coordinateMap k n).hom.comp
            (algebraMap (ProjectiveSpace.grading k n 0)
              (MvPolynomial (Fin (n + 1)) k)))) := by
  refine (coordinateOpenCover (projectiveIndex n) k).hom_ext _ _ fun i ↦ ?_
  rcases i with ⟨i⟩
  simp only [toProjectiveSpace, Projectivization.chartMap,
    Proj.toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc,
    Proj.basicOpenIsoSpec_inv_ι_assoc, Proj.awayι_toSpecZero, Iso.inv_comp_eq]
  simp only [coordinateOpenCover, Scheme.openCoverOfIsOpenCover_f, coordinateOpen,
    Scheme.isoOfEq_hom_ι_assoc, ← morphismRestrict_ι_assoc]
  congr 1
  simp only [basicOpenIsoSpecAway, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← Iso.eq_inv_comp,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, ← HomogeneousLocalization.algebraMap_eq]
  congr 2
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq _ (MvPolynomial (Fin (n + 1)) k),
    ← RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_assoc]

open PuncturedAffineSpace in
/-- The polynomial-spectrum comparison commutes with the maps to the affine base. -/
private theorem coordinateModelIso_inv_toBase (ι : Type u) (k : Type u) [CommRing k] :
    (coordinateModelIso ι k).inv ≫ PuncturedAffineSpace.toBase ι k =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        k →+* PuncturedAffineSpace.coordinateRing ι k)) := by
  simp only [coordinateModelIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    RingEquiv.toCommRingCatIso_inv, RingEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
    Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc, PuncturedAffineSpace.toBase,
    AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  congr 1
  ext r
  simp [MvPolynomial.renameEquiv_apply]

open PuncturedAffineSpace in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The ratio-coordinate construction of projectivization respects the affine base. -/
private theorem projectivization_toBase (k : Type u) [CommRing k] (n : ℕ) :
    toProjectiveSpace k n ≫ ProjectiveSpace.toSpec k n =
      (puncturedOpen (projectiveIndex n) k).ι ≫
        PuncturedAffineSpace.toBase (projectiveIndex n) k := by
  rw [ProjectiveSpace.toSpec, ← Category.assoc, projectivization_toSpecZero,
    Category.assoc]
  change (puncturedOpen (projectiveIndex n) k).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      ((Projectivization.coordinateMap k n).hom.comp
        (algebraMap (ProjectiveSpace.grading k n 0) (MvPolynomial (Fin (n + 1)) k)))) ≫
    Spec.map (CommRingCat.ofHom
      (ProjectiveSpace.degreeZeroRingEquiv k n).symm.toRingHom) = _
  rw [← Spec.map_comp]
  change (puncturedOpen (projectiveIndex n) k).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) ≫
      Projectivization.coordinateMap k n) = _
  have hC : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin (n + 1)) k) ≫
      Projectivization.coordinateMap k n =
      CommRingCat.ofHom (MvPolynomial.C :
          k →+* PuncturedAffineSpace.coordinateRing (projectiveIndex n) k) ≫
        globalSectionsComparison (projectiveIndex n) k := by
    ext r
    change (globalSectionsComparison (projectiveIndex n) k).hom
      ((MvPolynomial.renameEquiv k (Equiv.ulift : projectiveIndex n ≃ Fin (n + 1))).symm
        (MvPolynomial.C r)) =
      (globalSectionsComparison (projectiveIndex n) k).hom (MvPolynomial.C r)
    exact congrArg (globalSectionsComparison (projectiveIndex n) k).hom
      ((MvPolynomial.renameEquiv k
        (Equiv.ulift : projectiveIndex n ≃ Fin (n + 1))).symm.commutes r)
  erw [hC]
  simp only [globalSectionsComparison, coordinateRingToGlobalSections,
    coordinateRingGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, Spec.map_comp, Category.assoc]
  erw [← Scheme.toSpecΓ_naturality_assoc (puncturedOpen (projectiveIndex n) k).ι,
    ← Scheme.toSpecΓ_naturality_assoc (coordinateModelIso (projectiveIndex n) k).hom,
    toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  rw [← coordinateModelIso_inv_toBase (projectiveIndex n) k, Iso.hom_inv_id_assoc]

/-- The projectivized first-row morphism is over `Spec(k)`. -/
@[reassoc, stacks 01KX "rank-two projective structure map"]
theorem toProjectiveLine_toBase :
    toProjectiveLine k ≫ ProjectiveSpace.toSpec k 1 = toBase k := by
  have hrow : toAffinePlane k ≫ PuncturedAffinePlane.toBase k = toBase k := by
    change (Spec.map (CommRingCat.ofHom (toAffinePlaneComap k).toRingHom) ≫
      (PuncturedAffineSpace.coordinateModelIso index k).inv) ≫
        PuncturedAffineSpace.toBase index k = _
    rw [Category.assoc, coordinateModelIso_inv_toBase, ← Spec.map_comp]
    congr 1
    ext r
    exact (toAffinePlaneComap k).commutes r
  change (toPuncturedAffinePlane k ≫ PuncturedAffineSpace.toProjectiveSpace k 1) ≫
    ProjectiveSpace.toSpec k 1 = _
  rw [Category.assoc, projectivization_toBase, ← Category.assoc,
    toPuncturedAffinePlane_ι, hrow]

end CommRing

end GLTwo
end
end AlgebraicGeometry

