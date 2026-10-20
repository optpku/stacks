module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicStack.BaseChange

/-!
# Change of base scheme for relative separation axioms

The properties of being quasi-DM, quasi-separated, or separated over a scheme
are stable under change of base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsQuasiDMOver

/-- The change of base of an algebraic stack that is quasi-DM over its base
is quasi-DM over the new base. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsQuasiDMOver X'] :
    IsQuasiDMOver (baseChange g X') :=
  sorry

end IsQuasiDMOver

namespace IsQuasiSeparatedOver

/-- The change of base of an algebraic stack that is quasi-separated over its
base is quasi-separated over the new base. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsQuasiSeparatedOver X'] :
    IsQuasiSeparatedOver (baseChange g X') :=
  sorry

end IsQuasiSeparatedOver

namespace IsSeparatedOver

/-- The change of base of an algebraic stack that is separated over its base
is separated over the new base. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsSeparatedOver X'] :
    IsSeparatedOver (baseChange g X') :=
  sorry

end IsSeparatedOver

end AlgebraicGeometry.AlgebraicStack
