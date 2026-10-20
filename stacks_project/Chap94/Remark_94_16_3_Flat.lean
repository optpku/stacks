module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Flat groupoids in algebraic spaces

A groupoid in algebraic spaces is flat when its source and target maps are
flat morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces over `B` is flat when the source and target
maps `s, t : R ⟶ U` are flat morphisms of algebraic spaces. -/
class Flat {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Prop where
  /-- The source map is a flat morphism of algebraic spaces. -/
  source : AlgebraicSpace.Flat G.s.left
  /-- The target map is a flat morphism of algebraic spaces. -/
  target : AlgebraicSpace.Flat G.t.left

namespace Flat

/-- The discrete groupoid on an algebraic space over `B` is flat. -/
instance discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    Flat (GroupoidAlgebraicSpace.discrete U) := sorry

/-- The source map of a flat groupoid is a flat morphism of algebraic spaces. -/
instance instFlat_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : Flat G] :
    AlgebraicSpace.Flat G.s.left :=
  h.source

/-- The target map of a flat groupoid is a flat morphism of algebraic spaces. -/
instance instFlat_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : Flat G] :
    AlgebraicSpace.Flat G.t.left :=
  h.target

/-- A groupoid in algebraic spaces is flat if its source and target maps are
flat morphisms of algebraic spaces. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (hs : AlgebraicSpace.Flat G.s.left) (ht : AlgebraicSpace.Flat G.t.left) :
    Flat G := sorry

/-- A groupoid in algebraic spaces is flat if and only if its source and
target maps are flat morphisms of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Flat G ↔ AlgebraicSpace.Flat G.s.left ∧ AlgebraicSpace.Flat G.t.left :=
  sorry

/-- For a groupoid in algebraic spaces, flatness of the source map is
equivalent to flatness of the target map. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Flat G.s.left ↔ AlgebraicSpace.Flat G.t.left := sorry

end Flat

end AlgebraicGeometry.GroupoidAlgebraicSpace
