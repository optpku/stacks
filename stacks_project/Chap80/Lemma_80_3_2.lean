module

public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Morphisms of algebraic spaces are representable by algebraic spaces

A morphism of algebraic spaces over a scheme `S` is representable by algebraic
spaces in the sense of `representableByAlgebraicSpaces`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.3.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Then `f` is representable by algebraic spaces. -/
@[stacks 03BN]
theorem representableByAlgebraicSpaces.of_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : representableByAlgebraicSpaces f :=
  sorry

/-- The fibre product of a morphism of algebraic spaces along a Yoneda section from a
scheme over `S` is an algebraic space. -/
instance instIsAlgebraicSpace_pullback_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : Over S} (ξ : yoneda.obj U ⟶ Y.functorOfPoints) :
    IsAlgebraicSpace (pullback ξ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
