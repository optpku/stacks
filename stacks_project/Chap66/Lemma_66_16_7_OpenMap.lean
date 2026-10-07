module

public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Étale morphisms of algebraic spaces are open on points

An étale morphism of algebraic spaces over a scheme induces an open map of canonical
point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- An étale morphism of algebraic spaces induces an open map on canonical point spaces. -/
theorem isOpenMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    IsOpenMap (Points.map f) := sorry

/-- The image of an open set of points under an étale morphism of algebraic spaces is open. -/
theorem isOpen_image {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U : Set (Points X)} (hU : IsOpen U) : IsOpen (Points.map f '' U) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
