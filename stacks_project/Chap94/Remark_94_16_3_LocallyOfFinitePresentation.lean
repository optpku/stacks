/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Locally of finite presentation groupoids in algebraic spaces

A groupoid in algebraic spaces is locally of finite presentation when its
source and target maps are locally of finite presentation morphisms of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces over `B` is locally of finite presentation
when the source and target maps `s, t : R ⟶ U` are locally of finite
presentation morphisms of algebraic spaces. -/
class LocallyOfFinitePresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Prop where
  /-- The source map is locally of finite presentation. -/
  source : AlgebraicSpace.LocallyOfFinitePresentation G.s.left
  /-- The target map is locally of finite presentation. -/
  target : AlgebraicSpace.LocallyOfFinitePresentation G.t.left

namespace LocallyOfFinitePresentation

/-- The discrete groupoid on an algebraic space over `B` is locally of finite
presentation. -/
instance discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    LocallyOfFinitePresentation (GroupoidAlgebraicSpace.discrete U) := sorry

/-- The source map of a locally of finite presentation groupoid is locally of
finite presentation. -/
instance instLocallyOfFinitePresentation_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : LocallyOfFinitePresentation G] :
    AlgebraicSpace.LocallyOfFinitePresentation G.s.left :=
  h.source

/-- The target map of a locally of finite presentation groupoid is locally of
finite presentation. -/
instance instLocallyOfFinitePresentation_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [h : LocallyOfFinitePresentation G] :
    AlgebraicSpace.LocallyOfFinitePresentation G.t.left :=
  h.target

/-- A groupoid in algebraic spaces is locally of finite presentation if its
source and target maps are locally of finite presentation morphisms of
algebraic spaces. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (hs : AlgebraicSpace.LocallyOfFinitePresentation G.s.left)
    (ht : AlgebraicSpace.LocallyOfFinitePresentation G.t.left) :
    LocallyOfFinitePresentation G := sorry

/-- A groupoid in algebraic spaces is locally of finite presentation if and
only if its source and target maps are locally of finite presentation. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    LocallyOfFinitePresentation G ↔
      AlgebraicSpace.LocallyOfFinitePresentation G.s.left ∧
        AlgebraicSpace.LocallyOfFinitePresentation G.t.left :=
  sorry

/-- For a groupoid in algebraic spaces, the source map is locally of finite
presentation if and only if the target map is. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallyOfFinitePresentation G.s.left ↔
      AlgebraicSpace.LocallyOfFinitePresentation G.t.left := sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.GroupoidAlgebraicSpace
