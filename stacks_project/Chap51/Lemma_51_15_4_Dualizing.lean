module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.LocalExistence

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Typed compatibility check for local existence of dualizing complexes. -/
#check (AlgebraicGeometry.Scheme.LocallyHasDualizingComplex :
  (X : Scheme.{u}) → [IsLocallyNoetherian X] → Prop)

/- Typed compatibility check for the pointwise characterization. -/
#check (AlgebraicGeometry.Scheme.locallyHasDualizingComplex_iff :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X], LocallyHasDualizingComplex X ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ K : RingedSpace.ModuleDerived U.toScheme.toRingedSpace,
          IsDualizingComplex K)

end AlgebraicGeometry.Scheme
