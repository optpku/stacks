/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent

/-!
# Fibres along étale neighbourhoods

Base change to an étale neighbourhood and a factorization of its residue-field
point induce a canonical comparison of fibres. For an elementary neighbourhood
of a decent algebraic space, the distinguished fibre is isomorphic to the original fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison from the residue-field fibre after base change along a scheme
point to the fibre over a specified field-valued point of the target.  It is the
composite of the two canonical comparison maps, with no residue-field representative
selected from an existence theorem. -/
def fiberOver_neighborhoodComparison {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {V : Over S} (a : ofOver V ⟶ X) (v : V.left)
    {q : FieldValuedPoint X}
    (φ : ((FieldValuedPoint.ofScheme
      (Scheme.FieldValuedPoint.residuePoint v)).map a).Factorization q) :
    fieldFiber (overPullbackSnd a (Over.mk f))
        (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) ⟶
      fieldFiber f q :=
  fiberOver_mapSquare f a (overPullbackFst a (Over.mk f))
      (overPullbackSnd a (Over.mk f))
      (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v))
      (ReasLibPullback.isPullback f a).w ≫
    fiberOver_factor f φ

/-- The comparison commutes with the source projection and induces the supplied
map of residue spectra on the second projection. -/
theorem fiberOver_neighborhoodComparison_spec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) {V : Over S}
    (a : ofOver V ⟶ X) (v : V.left) {q : FieldValuedPoint X}
    (φ : ((FieldValuedPoint.ofScheme
      (Scheme.FieldValuedPoint.residuePoint v)).map a).Factorization q) :
    fiberOver_neighborhoodComparison f a v φ ≫ fieldFiberι f q =
        fieldFiberι (overPullbackSnd a (Over.mk f))
            (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) ≫
          overPullbackFst a (Over.mk f) ∧
      fiberOver_neighborhoodComparison f a v φ ≫ fieldFiberToSpec f q =
        fieldFiberToSpec (overPullbackSnd a (Over.mk f))
            (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) ≫
          ofOverHomMk φ.schemeHom φ.fac_structure := by
  let p := FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)
  have hs := fiberOver_mapSquare_spec f a (overPullbackFst a (Over.mk f))
    (overPullbackSnd a (Over.mk f)) p (ReasLibPullback.isPullback f a).w
  have hf := fiberOver_factor_spec f φ
  let m := fiberOver_mapSquare f a (overPullbackFst a (Over.mk f))
    (overPullbackSnd a (Over.mk f)) p (ReasLibPullback.isPullback f a).w
  constructor
  · exact ((Category.assoc _ _ _).trans
      (congrArg (fun k ↦ m ≫ k) hf.1)).trans hs.1
  · exact (((Category.assoc _ _ _).trans
      (congrArg (fun k ↦ m ≫ k) hf.2)).trans (Category.assoc _ _ _).symm).trans
      (congrArg (fun k ↦ k ≫ ofOverHomMk φ.schemeHom φ.fac_structure) hs.2)

/-- The comparison is an isomorphism whenever its map of representative spectra
is an isomorphism. -/
theorem isIso_fiberOver_neighborhoodComparison {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) {V : Over S}
    (a : ofOver V ⟶ X) (v : V.left) {q : FieldValuedPoint X}
    (φ : ((FieldValuedPoint.ofScheme
      (Scheme.FieldValuedPoint.residuePoint v)).map a).Factorization q)
    [IsIso φ.schemeHom] : IsIso (fiberOver_neighborhoodComparison f a v φ) := by
  let p := FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)
  letI := isIso_fiberOver_mapSquare f a (overPullbackFst a (Over.mk f))
    (overPullbackSnd a (Over.mk f)) p (ReasLibPullback.isPullback f a).w
    (ReasLibPullback.isPullback f a)
  letI := isIso_fiberOver_factor f φ
  dsimp only [fiberOver_neighborhoodComparison]
  infer_instance

/-- Base change along an elementary étale neighbourhood of a decent algebraic
space preserves the fibre over the distinguished residue-field point. -/
theorem fiberOver_elementaryNeighborhood {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] (f : Y ⟶ X) {x : Points X} (U : EtaleNeighborhood X x)
    (hU : U.IsElementary) :
    Nonempty
      (fieldFiber (overPullbackSnd U.hom (Over.mk f))
          (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint U.point)) ≅
        fieldFiber f (FieldValuedPoint.residuePoint x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
