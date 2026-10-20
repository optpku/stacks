module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType

/-!
# Closed-immersion factorizations of finite type morphisms of algebraic stacks

A finite type quasi-separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space factors, over the target, through
a closed immersion into an algebraic stack of finite presentation.

If the original morphism is separated, the structure morphism of the
intermediate algebraic stack can also be chosen separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A finite type quasi-separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space factors, over the target, through
a closed immersion into an algebraic stack of finite presentation. -/
theorem exists_closedImmersion_factorization_of_finiteType
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y.toGroupoids) [FiniteType f] [QuasiSeparated f] :
    ∃ (X' : GroupoidsOver S) (hX' : AlgebraicStack X')
      (f' : X' ⟶ Y.toGroupoids) (hf' : FinitePresentation f')
      (i : X ⟶ X') (hi : Groupoids.Hom.ClosedImmersion i),
      Nonempty (i ≫ f' ≅ f) :=
  sorry

/-- A finite type separated morphism from an algebraic stack to a
quasi-compact quasi-separated algebraic space factors, over the target, through
a closed immersion into an algebraic stack whose structure morphism is separated
and of finite presentation. -/
theorem exists_closedImmersion_factorization_of_finiteType_separated
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y.toGroupoids) [FiniteType f] [Separated f] :
    ∃ (X' : GroupoidsOver S) (hX' : AlgebraicStack X')
      (f' : X' ⟶ Y.toGroupoids) (hf' : FinitePresentation f')
      (hf'separated : Separated f')
      (i : X ⟶ X') (hi : Groupoids.Hom.ClosedImmersion i),
      Nonempty (i ≫ f' ≅ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
