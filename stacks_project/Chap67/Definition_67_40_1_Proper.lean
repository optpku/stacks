module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Proper morphisms of algebraic spaces

A morphism of algebraic spaces is proper when it is separated, of finite type,
and universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is proper if it is separated, of finite type,
and universally closed. -/
@[mk_iff]
class Proper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends Separated f, FiniteType f, UniversallyClosed f

namespace Proper

/-- A proper morphism of algebraic spaces is separated, of finite type, and
universally closed. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] :
    Separated f ∧ FiniteType f ∧ UniversallyClosed f :=
  sorry

/-- The identity morphism of an algebraic space is proper. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Proper (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is proper. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : Proper f :=
  sorry

/-- A separated, finite type, and universally closed morphism of algebraic
spaces is proper. -/
instance instOfSeparatedFiniteTypeUniversallyClosed {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] [FiniteType f]
    [UniversallyClosed f] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
