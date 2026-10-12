/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

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
