/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Smooth groupoids in algebraic spaces

A groupoid in algebraic spaces is smooth when its source and target maps are
smooth morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces over `B` is smooth when the source and target
maps `s, t : R ⟶ U` are smooth morphisms of algebraic spaces. This does not
imply that the quotient stack `[U / R]` is smooth over `S` or `B`. -/
class Smooth {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Prop where
  /-- The source map is a smooth morphism of algebraic spaces. -/
  source : AlgebraicSpace.Smooth G.s.left
  /-- The target map is a smooth morphism of algebraic spaces. -/
  target : AlgebraicSpace.Smooth G.t.left

namespace Smooth

/-- The discrete groupoid on an algebraic space over `B` is smooth. -/
instance discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    Smooth (GroupoidAlgebraicSpace.discrete U) := sorry

/-- The source map of a smooth groupoid is a smooth morphism of algebraic spaces. -/
instance instSmooth_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : Smooth G] :
    AlgebraicSpace.Smooth G.s.left :=
  h.source

/-- The target map of a smooth groupoid is a smooth morphism of algebraic spaces. -/
instance instSmooth_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : Smooth G] :
    AlgebraicSpace.Smooth G.t.left :=
  h.target

/-- A groupoid in algebraic spaces is smooth if its source and target maps are
smooth morphisms of algebraic spaces. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (hs : AlgebraicSpace.Smooth G.s.left) (ht : AlgebraicSpace.Smooth G.t.left) :
    Smooth G := sorry

/-- A groupoid in algebraic spaces is smooth if and only if its source and
target maps are smooth morphisms of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Smooth G ↔ AlgebraicSpace.Smooth G.s.left ∧ AlgebraicSpace.Smooth G.t.left :=
  sorry

/-- For a groupoid in algebraic spaces, smoothness of the source map is
equivalent to smoothness of the target map. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Smooth G.s.left ↔ AlgebraicSpace.Smooth G.t.left := sorry

end Smooth

end AlgebraicGeometry.GroupoidAlgebraicSpace
