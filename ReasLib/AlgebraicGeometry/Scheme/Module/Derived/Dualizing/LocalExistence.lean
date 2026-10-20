module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme locally has a dualizing complex when every point has an open
neighborhood carrying a dualizing complex. -/
def LocallyHasDualizingComplex (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ K : RingedSpace.ModuleDerived U.toScheme.toRingedSpace,
      IsDualizingComplex K

/-- The pointwise open-neighborhood characterization of local dualizing complexes. -/
theorem locallyHasDualizingComplex_iff {X : Scheme.{u}} [IsLocallyNoetherian X] :
    LocallyHasDualizingComplex X ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        ∃ K : RingedSpace.ModuleDerived U.toScheme.toRingedSpace,
          IsDualizingComplex K := sorry

end AlgebraicGeometry.Scheme
