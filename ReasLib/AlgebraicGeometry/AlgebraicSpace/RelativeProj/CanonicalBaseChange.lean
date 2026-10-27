/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChangeComparison
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# The actual relative-Proj base-change morphism on points

On quasi-compact tests the maps transport genuine quadruples in the two
directions. On arbitrary tests they use the specified compatible systems over
quasi-compact opens. No compactness hypothesis is imposed on the test scheme
of the resulting natural isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (g : X' ⟶ X)
variable {𝒜 𝒜'} {deg : DegreePieces 𝒜} {deg' : DegreePieces 𝒜'}
variable (hAlg : AlgebraPullback g deg deg')
variable {F : ProjFunctor X 𝒜} (hF : F.IsAssociatedToQuadruples deg)
variable {F' : ProjFunctor X' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')

/-- On a quasi-compact test, push the representing quadruple along the base map. -/
def baseChangeForwardQc (T : Over S) [CompactSpace T.left]
    (x : F'.toFunctor.obj (op T)) : F.toFunctor.obj (op T) :=
  hF.pointOf T (hAlg.forwardQuadruple (hF'.quadrupleOf T x))

/-- On any test scheme, glue the actual images on quasi-compact opens. -/
def baseChangeForward (T : Over S) (x : F'.toFunctor.obj (op T)) :
    F.toFunctor.obj (op T) :=
  (hF.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.mk
      (fun V _ ↦ baseChangeForwardQc g hAlg hF hF' (openOver T V)
        (F'.toFunctor.map (op (openOverι T V)) x)) sorry)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the glued forward map recovers the specified map on a qc open. -/
theorem baseChangeForward_restrict (T : Over S) (x : F'.toFunctor.obj (op T))
    (V : T.left.Opens) [CompactSpace V.toScheme] :
    F.toFunctor.map (op (openOverι T V)) (baseChangeForward g hAlg hF hF' T x) =
      baseChangeForwardQc g hAlg hF hF' (openOver T V)
        (F'.toFunctor.map (op (openOverι T V)) x) := by
  rw [← hF.qcLimit_restrict]
  exact congrArg (fun q ↦ q.restrict V) ((hF.qcLimit T).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
private theorem baseChangeForwardQc_base (T : Over S) [CompactSpace T.left]
    (x : F'.toFunctor.obj (op T)) :
    F.baseMap.app (op T) (baseChangeForwardQc g hAlg hF hF' T x) =
      g.app (op T) (F'.baseMap.app (op T) x) := by
  calc
    _ = (hAlg.forwardQuadruple (hF'.quadrupleOf T x)).morphism.app (op T) (𝟙 T) :=
      (hF.base_eq T _ _ (hF.associated_pointOf T _)).symm
    _ = g.app (op T) ((hF'.quadrupleOf T x).morphism.app (op T) (𝟙 T)) := rfl
    _ = _ := congrArg (fun t ↦ g.app (op T) t)
      (hF'.base_eq T _ _ (hF'.associated_quadrupleOf T x))

set_option backward.isDefEq.respectTransparency false in
private theorem points_ext_qc {Y : AlgebraicSpace S} (T : Over S)
    {x y : Y.functorOfPoints.obj (op T)}
    (h : ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      Y.functorOfPoints.map (op (openOverι T V)) x =
        Y.functorOfPoints.map (op (openOverι T V)) y) : x = y := by
  have hcover :
      Sieve.ofArrows (fun V : T.left.affineOpens ↦ openOver T (V : T.left.Opens))
        (fun V ↦ openOverι T (V : T.left.Opens)) ∈ (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (T.left.openCoverOfIsOpenCover (fun V : T.left.affineOpens ↦ (V : T.left.Opens))
        (iSup_affineOpens_eq_top T.left)).mem_grothendieckTopology
  have hs := (isSheaf_iff_isSheaf_of_type _ _).mp Y.isSheaf
  apply (hs.isSheafFor _ hcover).isSeparatedFor.ext
  rintro Z f ⟨V⟩
  exact h V

/-- Pushalong of the classified quadruples defines a natural transformation. -/
def baseChangeForwardNat : F'.toFunctor ⟶ F.toFunctor where
  app T := TypeCat.ofHom (baseChangeForward g hAlg hF hF' T.unop)
  naturality := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The forward point map has the correct base point. -/
theorem baseChangeForwardNat_over :
    F'.baseMap ≫ g = baseChangeForwardNat g hAlg hF hF' ≫ F.baseMap := by
  ext T x
  apply points_ext_qc T.unop
  intro V _
  change X.functorOfPoints.map (op (openOverι T.unop V))
      (g.app T (F'.baseMap.app T x)) =
    X.functorOfPoints.map (op (openOverι T.unop V))
      (F.baseMap.app T (baseChangeForward g hAlg hF hF' T.unop x))
  rw [← g.naturality_apply, ← F'.baseMap.naturality_apply,
    ← F.baseMap.naturality_apply, baseChangeForward_restrict]
  exact (baseChangeForwardQc_base g hAlg hF hF' (openOver T.unop V) _).symm

/-- The actual forward map into the sheaf fibre product is the categorical
pullback lift of the base point and transported quadruple class. -/
def canonicalBaseChangeHom : toAlgebraicSpace F' hF' ⟶ fibreProduct g hF :=
  pullback.lift F'.baseMap (baseChangeForwardNat g hAlg hF hF')
    (baseChangeForwardNat_over g hAlg hF hF')

set_option backward.isDefEq.respectTransparency false in
/-- The base point of a fibre-product section lifts the structure map of its
represented quadruple, by the pullback equation and the association base law. -/
theorem inverseQuadruple_base (T : Over S) [CompactSpace T.left]
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) :
    pointHom ((fibreProduct_fst g hF).app (op T) y) ≫ g =
      (hF.quadrupleOf T ((fibreProduct_snd g hF).app (op T) y)).morphism := by
  apply (yonedaEquiv (C := Over S) (F := X.functorOfPoints)).injective
  calc
    _ = g.app (op T)
        (yonedaEquiv (pointHom ((fibreProduct_fst g hF).app (op T) y))) :=
      yonedaEquiv_comp (C := Over S) _ g
    _ = g.app (op T) ((fibreProduct_fst g hF).app (op T) y) :=
      congrArg (fun t ↦ g.app (op T) t) (Equiv.apply_symm_apply _ _)
    _ = F.baseMap.app (op T) ((fibreProduct_snd g hF).app (op T) y) :=
      congrArg (fun k ↦ k.app (op T) y)
        (pullback.condition (C := ((Over S)ᵒᵖ ⥤ Type u)) (f := g)
          (g := F.baseMap))
    _ = _ := (hF.base_eq T _ _ (hF.associated_quadrupleOf T _)).symm

/-- The inverse point map on a quasi-compact test uses the actual inverse
transport of the homogeneous algebra maps. -/
def baseChangeInverseQc (T : Over S) [CompactSpace T.left]
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) : F'.toFunctor.obj (op T) :=
  hF'.pointOf T
    (hAlg.inverseQuadruple
      (pointHom ((fibreProduct_fst g hF).app (op T) y))
      (hF.quadrupleOf T ((fibreProduct_snd g hF).app (op T) y))
      (inverseQuadruple_base g hF T y))

/-- The inverse on arbitrary tests is assembled from the specified qc-open limit. -/
def baseChangeInverse (T : Over S)
    (y : (fibreProduct g hF).functorOfPoints.obj (op T)) : F'.toFunctor.obj (op T) :=
  (hF'.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.mk
      (fun V _ ↦ baseChangeInverseQc g hAlg hF hF' (openOver T V)
        ((fibreProduct g hF).functorOfPoints.map (op (openOverι T V)) y)) sorry)

/-- The actual inverse map is natural in the test scheme. -/
def canonicalBaseChangeInv : fibreProduct g hF ⟶ toAlgebraicSpace F' hF' where
  app T := TypeCat.ofHom (baseChangeInverse g hAlg hF hF' T.unop)
  naturality := sorry

/-- Quadruple pushalong followed by its inverse fixes the classified point. -/
theorem canonicalBaseChange_hom_inv_id :
    canonicalBaseChangeHom g hAlg hF hF' ≫ canonicalBaseChangeInv g hAlg hF hF' =
      𝟙 (toAlgebraicSpace F' hF') := sorry

/-- Inverse quadruple transport followed by pushalong fixes both fibre-product coordinates. -/
theorem canonicalBaseChange_inv_hom_id :
    canonicalBaseChangeInv g hAlg hF hF' ≫ canonicalBaseChangeHom g hAlg hF hF' =
      𝟙 (fibreProduct g hF) := sorry

/-- Relative-Proj base change with explicit mutually inverse point maps. -/
def canonicalBaseChangeIso : toAlgebraicSpace F' hF' ≅ fibreProduct g hF where
  hom := canonicalBaseChangeHom g hAlg hF hF'
  inv := canonicalBaseChangeInv g hAlg hF hF'
  hom_inv_id := canonicalBaseChange_hom_inv_id g hAlg hF hF'
  inv_hom_id := canonicalBaseChange_inv_hom_id g hAlg hF hF'

set_option backward.isDefEq.respectTransparency false in
/-- The constructed isomorphism is over the changed base. -/
theorem canonicalBaseChangeIso_fst :
    (canonicalBaseChangeIso g hAlg hF hF').hom ≫ fibreProduct_fst g hF =
      toAlgebraicSpace_hom F' hF' := by
  change pullback.lift F'.baseMap (baseChangeForwardNat g hAlg hF hF')
    (baseChangeForwardNat_over g hAlg hF hF') ≫
      pullback.fst (C := ((Over S)ᵒᵖ ⥤ Type u)) g F.baseMap = F'.baseMap
  exact pullback.lift_fst (C := ((Over S)ᵒᵖ ⥤ Type u)) _ _ _

/-- The canonical isomorphism acts by the forward and inverse quadruple formulas. -/
theorem canonicalBaseChangeIso_formula :
    ActsByQuadrupleFormula g hAlg hF hF' (canonicalBaseChangeIso g hAlg hF hF') := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
