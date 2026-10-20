module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import stacks_project.Chap48.Lemma_48_2_1

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Typed compatibility check for the promoted scheme-level predicate. -/
#check (IsDualizingComplex :
  {X : Scheme.{u}} → [IsLocallyNoetherian X] →
    RingedSpace.ModuleDerived X.toRingedSpace → Prop)

end AlgebraicGeometry.Scheme
