module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification

/-!
# Sheafification on small standard scheme sites

This module supplies sheafification properties for the canonical Zariski and
étale small sites and for the small presentations of all five standard sites.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallStandardTopology

/-- Abelian-group-valued weak sheafification exists on either canonical small
standard site. -/
instance instHasWeakSheafify (σ : SmallStandardTopology) (S : Scheme.{u}) :
    HasWeakSheafify (σ.topology S) AddCommGrpCat.{u} := sorry

/-- Sheafification equivalences on either canonical small standard site are
exactly the locally bijective morphisms. -/
instance instWEqualsLocallyBijective
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (σ.topology S).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued weak sheafification exists on twice-iterated slices
of either canonical small standard site. -/
instance instHasWeakSheafifyOverOver
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ∀ U : σ.site S, ∀ V : Over U,
      HasWeakSheafify (((σ.topology S).over U).over V) AddCommGrpCat.{u} := sorry

/-- On twice-iterated slices of either canonical small standard site,
sheafification equivalences are exactly the locally bijective morphisms. -/
instance instWEqualsLocallyBijectiveOverOver
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ∀ U : σ.site S, ∀ V : Over U,
      (((σ.topology S).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := sorry

end AlgebraicGeometry.SmallStandardTopology

namespace AlgebraicGeometry.StandardTopology.Small

/-- Abelian-group-valued weak sheafification exists on every small standard
site. -/
instance instHasWeakSheafify (τ : StandardTopology) (S : Scheme.{u}) :
    HasWeakSheafify (topology τ S) AddCommGrpCat.{u} := sorry

/-- Sheafification equivalences on every small standard site are exactly the
locally bijective morphisms. -/
instance instWEqualsLocallyBijective (τ : StandardTopology) (S : Scheme.{u}) :
    (topology τ S).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued weak sheafification exists on every slice of a small
standard site. -/
instance instHasWeakSheafifyOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S,
      HasWeakSheafify ((topology τ S).over U) AddCommGrpCat.{u} := sorry

/-- On every slice of a small standard site, sheafification equivalences are
exactly the locally bijective morphisms. -/
instance instWEqualsLocallyBijectiveOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S,
      ((topology τ S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

/-- Abelian-group-valued weak sheafification exists on twice-iterated slices
of every small standard site. -/
instance instHasWeakSheafifyOverOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S, ∀ V : Over U,
      HasWeakSheafify (((topology τ S).over U).over V) AddCommGrpCat.{u} := sorry

/-- On twice-iterated slices of every small standard site, sheafification
equivalences are exactly the locally bijective morphisms. -/
instance instWEqualsLocallyBijectiveOverOver
    (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : site τ S, ∀ V : Over U,
      (((topology τ S).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := sorry

/-- Weak sheafification at the lifted coefficient universe exists on every
small standard site. -/
instance instCommHasWeakSheafify (τ : StandardTopology) (S : Scheme.{u}) :
    HasWeakSheafify (topology τ S) AddCommGrpCat.{u + 1} := sorry

/-- At the lifted coefficient universe, sheafification equivalences on every
small standard site are exactly the locally bijective morphisms. -/
instance instCommWEqualsLocallyBijective
    (τ : StandardTopology) (S : Scheme.{u}) :
    (topology τ S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := sorry

end AlgebraicGeometry.StandardTopology.Small
