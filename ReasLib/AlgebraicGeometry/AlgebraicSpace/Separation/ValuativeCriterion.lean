module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Valuative criterion of separatedness for algebraic spaces

A quasi-separated morphism of algebraic spaces is separated if it satisfies the
uniqueness part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Separated

/-- A quasi-separated morphism of algebraic spaces that satisfies the uniqueness
part of the valuative criterion is separated. -/
@[instance 100]
theorem of_valuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [ValuativeCriterion.Uniqueness f] : Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Separated
