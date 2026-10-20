module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- The regular-model bundle is provided by its mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Hom.RegularModel :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom], Type (u + 1))

/- The explicit constructor preserves the structural data and generic-fibre identification. -/
#check (AlgebraicGeometry.Scheme.Hom.RegularModel.ofData :
  ∀ {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : SchemeOverField K} [Curve C] [Smooth C.hom] [Projective C.hom]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (h_noetherian : IsNoetherian X) (h_flat : Flat f) (h_finiteType : FiniteType f)
    (h_proper : IsProper f) (h_regular : Scheme.Regular X)
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
    RegularModel R K C)

end AlgebraicGeometry.Scheme.Hom
