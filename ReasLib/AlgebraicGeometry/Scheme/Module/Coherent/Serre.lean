module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A bundled coherent module satisfies Serre's condition `(S_k)` when its stalks satisfy
the corresponding depth lower bounds. -/
def coherentSatisfiesSerreConditionS
    (F : RingedSpace.Coh X.toRingedSpace) (k : ℕ) : Prop :=
  @satisfiesSerreConditionS X _ F.obj F.property k

/-- Serre's condition for a bundled coherent module is the Serre condition for its
underlying module with the given coherence proof. -/
theorem coherentSatisfiesSerreConditionS_iff
    (F : RingedSpace.Coh X.toRingedSpace) (k : ℕ) :
    coherentSatisfiesSerreConditionS F k ↔
      @satisfiesSerreConditionS X _ F.obj F.property k :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules
