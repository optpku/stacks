module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

/-!
# Sheafification on slices of standard scheme sites

This module supplies the sheafification properties needed for sheaves of modules on
slices of the standard big, small Zariski, and small étale sites of a scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Abelian-group-valued weak sheafification exists on every slice of a standard big
scheme site. -/
instance over_hasWeakSheafify (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      HasWeakSheafify ((τ.overTopology S).over U) AddCommGrpCat.{u} := sorry

/-- On every slice of a standard big scheme site, sheafification equivalences are
exactly the locally bijective morphisms. -/
instance over_wEqualsLocallyBijective (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      ((τ.overTopology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- Abelian-group-valued weak sheafification exists on every slice of the small
Zariski site of a scheme. -/
instance over_hasWeakSheafify (S : Scheme.{u}) :
    ∀ U : S.smallZariskiSite,
      HasWeakSheafify (S.smallZariskiTopology.over U) AddCommGrpCat.{u} := sorry

/-- On every slice of the small Zariski site, sheafification equivalences are exactly
the locally bijective morphisms. -/
instance over_wEqualsLocallyBijective (S : Scheme.{u}) :
    ∀ U : S.smallZariskiSite,
      (S.smallZariskiTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

end AlgebraicGeometry.Scheme.Zariski.Small

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- Abelian-group-valued weak sheafification exists on every slice of the small
étale site of a scheme. -/
instance over_hasWeakSheafify (S : Scheme.{u}) :
    ∀ U : S.Etale,
      HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u} := sorry

/-- On every slice of the small étale site, sheafification equivalences are exactly
the locally bijective morphisms. -/
instance over_wEqualsLocallyBijective (S : Scheme.{u}) :
    ∀ U : S.Etale,
      (S.smallEtaleTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

end AlgebraicGeometry.Scheme.Etale.Small
