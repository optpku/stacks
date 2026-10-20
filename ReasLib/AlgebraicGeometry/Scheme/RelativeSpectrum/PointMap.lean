module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.MapOver

/-!
# Actual morphisms from relative-spectrum points

The inverse direction of the hom correspondence is constructed on the pulled
back affine cover using the supplied algebra-map components and native Γ–Spec.
It does not extract a morphism from a representability certificate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- The actual scheme map supplied by a relative-spectrum point on one affine base open. -/
def relativeSpectrumPointMapAffine (A : S.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (U : S.affineOpens) : pullback p.1 (U : S.Opens).ι ⟶ (relativeSpectrumOver A).scheme :=
  (pullbackRestrictIsoRestrict p.1 (U : S.Opens)).hom ≫
    (p.1 ⁻¹ᵁ (U : S.Opens)).toSpecΓ ≫
      Spec.map ((InducedCategory.Hom.hom p.2.right).app (op (U : S.Opens))) ≫
        colimit.ι (relativeSpectrumNativeGluingData A).functor U

/-- Glue the point's actual affine maps to a morphism into the constructed relative spectrum. -/
def relativeSpectrumPointMap (A : S.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    T ⟶ (relativeSpectrumOver A).scheme :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected (S.directedAffineCover.pullback₁ p.1)
    (fun (U : S.affineOpens) ↦ relativeSpectrumPointMapAffine A p U) sorry

/-- The point-to-morphism construction preserves the given base morphism. -/
theorem relativeSpectrumPointMap_toBase (A : S.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointMap A p ≫ (relativeSpectrumOver A).π = p.1 := sorry

/-- The point-to-morphism map computes on each pulled-back affine base chart. -/
theorem relativeSpectrumPointMap_affine (A : S.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (U : S.affineOpens) :
    pullback.fst p.1 (U : S.Opens).ι ≫ relativeSpectrumPointMap A p =
      relativeSpectrumPointMapAffine A p U := sorry

/-- Both directions of the hom correspondence have their actual geometric and algebra-map data. -/
def relativeSpectrumHomEquiv (A : S.QcAlgebraUnder) (T : Scheme.{u}) :
    (T ⟶ (relativeSpectrumOver A).scheme) ≃ relativeSpectrumPair A T where
  toFun t := relativeSpectrumPairPullbackMap A t (relativeSpectrumOver A).point
  invFun := relativeSpectrumPointMap A
  left_inv := sorry
  right_inv := sorry

/-- The inverse hom correspondence is exactly the explicit affine-glued point map. -/
theorem relativeSpectrumHomEquiv_symm_apply (A : S.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) :
    (relativeSpectrumHomEquiv A T).symm p = relativeSpectrumPointMap A p := rfl

end AlgebraicGeometry.Scheme
