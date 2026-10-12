/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Surjective morphisms of algebraic spaces

A morphism of algebraic spaces is surjective when the induced map of associated
point spaces is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is surjective if the induced map of associated
point spaces is surjective. -/
@[mk_iff]
class Surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The induced map on points is surjective. -/
  map_surjective : Function.Surjective (Points.map f)

namespace Surjective

/-- The identity morphism of an algebraic space is surjective. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Surjective (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Surjective f := sorry

/-- A surjective morphism of algebraic spaces induces a surjective map of associated
point spaces. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (Points.map f) := sorry

/-- A morphism of algebraic spaces is surjective as soon as the induced map of
associated point spaces is surjective. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Function.Surjective (Points.map f)) : Surjective f := sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace
