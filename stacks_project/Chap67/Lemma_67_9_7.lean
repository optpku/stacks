module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed

/-!
# Universally closed morphisms of algebraic spaces are quasi-compact

A universally closed morphism of algebraic spaces over a scheme is
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- Lemma 67.9.7: a universally closed morphism of algebraic spaces over a
scheme `S` is quasi-compact. -/
@[stacks 04XW]
instance of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] : QuasiCompact f := sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
