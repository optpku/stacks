module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ClosedOpen

/-!
# Compatibility checks for the complementary closed/open construction
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated CategoryTheory.Localization
open AlgebraicGeometry ComplexShape

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

#check (etaleModuleSheaf_hasZeroMorphisms : ∀ (Y : Scheme.{u}) (Λ : Type v),
  [CommRing Λ] → [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))] →
    HasZeroMorphisms (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)))
#check moduleClosedOpenLower
#check moduleClosedOpenLower_obj
#check moduleClosedOpenClosed
#check moduleClosedOpenClosed_obj
#check moduleClosedOpenCounitNat
#check moduleClosedOpenUnitNat
#check moduleClosedOpenCounit
#check moduleClosedOpenUnit
#check moduleClosedOpen_comp_zero
#check moduleClosedOpenShortComplex
#check moduleClosedOpenShortComplex_f
#check moduleClosedOpenShortComplex_g
#check moduleClosedOpenShortComplex_shortExact
#check moduleClosedOpenCochainCounit
#check moduleClosedOpenCochainUnit
#check moduleClosedOpenCochain_comp_zero
#check moduleClosedOpenCochainShortComplex
#check moduleClosedOpenCochainShortComplex_shortExact
#check etaleDerivedClosedOpenCounit
#check etaleDerivedClosedOpenClosed
#check etaleDerivedClosedOpenClosed_obj
#check etaleDerivedClosedOpenUnit
#check etaleDerivedClosedOpenδ
#check etaleDerivedClosedOpenTriangle
#check etaleDerivedClosedOpenTriangle_obj₁
#check etaleDerivedClosedOpenTriangle_obj₂
#check etaleDerivedClosedOpenTriangle_obj₃
#check etaleDerivedClosedOpenTriangle_mor₁
#check etaleDerivedClosedOpenTriangle_mor₂
#check etaleDerivedClosedOpenTriangle_mor₃
#check etaleDerivedClosedOpenTriangle_distinguished

end AlgebraicGeometry.Scheme.Etale
