/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.AffineOver.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteComparison

/-!
# Comparison with quasi-coherent derived modules on a scheme

The all-affine comparison category maps canonically to derived structure-sheaf modules with
quasi-coherent cohomology by restriction to affine opens and the standard small-site
equivalences.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.AffineOverQC

/-- The canonical comparison from quasi-coherent derived modules on all affine schemes over `S`
to derived `𝒪_S`-modules with quasi-coherent cohomology. -/
noncomputable def comparison (S : Scheme.{u}) :
    AffineOverQC S ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty S.toRingedSpace) :=
  restrictToAffine S ⋙
    (affineQCEquivalence S).inverse ⋙
    (affineTopologyEquivalence S).inverse ⋙
    (affineZariskiEquivalence S).inverse ⋙
    (smallZariskiEquivalence S).inverse

/-- The canonical comparison from the all-affine presentation to quasi-coherent derived
`𝒪_S`-modules is an equivalence. -/
instance comparisonIsEquivalence (S : Scheme.{u}) :
    (comparison S).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.AffineOverQC
