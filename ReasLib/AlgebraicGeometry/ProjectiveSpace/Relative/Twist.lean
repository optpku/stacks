module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Twists on relative projective space

This file specializes integral tensor twists to the tautological sheaf of a chosen relative
projective space.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOver

variable {S : Scheme.{u}} {n : ℕ} (P : ProjectiveSpaceOver S n)

/-- The twist of a module on relative projective space by an integral tensor power of the
tautological sheaf. -/
noncomputable abbrev twist (F : P.scheme.Modules) (d : ℤ) : P.scheme.Modules :=
  @Scheme.Modules.twistByTensorPower P.scheme P.tautologicalSheaf F
    P.tautologicalSheaf_isInvertible d

end AlgebraicGeometry.ProjectiveSpaceOver
