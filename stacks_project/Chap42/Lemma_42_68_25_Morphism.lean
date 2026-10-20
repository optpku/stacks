module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Compatibility check for the explicit morphism type used by source-facing consumers. -/
#check (CategoryTheory.TwoPeriodicEndomorphism.Hom :
  TwoPeriodicEndomorphism C → TwoPeriodicEndomorphism C → Type v)

end CategoryTheory.TwoPeriodicEndomorphism
