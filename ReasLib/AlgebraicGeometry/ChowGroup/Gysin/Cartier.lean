module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme.AssociatedSheaf

/-!
# Gysin pullback along an effective Cartier divisor

This file defines Cartier Gysin pullback by transporting zero-section Gysin pullback
through the canonical identification with the divisor subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Gysin pullback along an effective Cartier divisor, obtained from the canonical section
of its associated invertible sheaf and the canonical zero-scheme identification. -/
noncomputable def cartierGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (n : ℤ) :
    RelativeChow δ X n →+
      RelativeChow δ (Over.mk (D.subschemeι ≫ X.hom)) (n - 1) :=
  (map δ
    (Over.mk (Scheme.zeroSchemeι D.associatedSheaf D.canonicalSection ≫ X.hom))
    (Over.mk (D.subschemeι ≫ X.hom)) D.associatedZeroSchemeOverIso.hom (n - 1)).comp
      (gysin δ X D.associatedSheaf D.canonicalSection n)

/-- Cartier Gysin pullback on a Chow class is the zero-section Gysin class transported
through the canonical zero-scheme identification. -/
theorem cartierGysin_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (n : ℤ) (c : CycleGroup X.left (X.hom.relativeDimensionFunction δ) n) :
    cartierGysin δ X D n
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance n c) =
      map δ
        (Over.mk (Scheme.zeroSchemeι D.associatedSheaf D.canonicalSection ≫ X.hom))
        (Over.mk (D.subschemeι ≫ X.hom)) D.associatedZeroSchemeOverIso.hom (n - 1)
        (Scheme.Modules.gysin X.hom δ D.associatedSheaf D.canonicalSection (n - 1)
          (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
            (Int.sub_add_cancel n 1).symm c)) := sorry

end AlgebraicGeometry.ChowGroup
