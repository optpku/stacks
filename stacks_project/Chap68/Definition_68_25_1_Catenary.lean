module

public import ReasLib.Topology.Catenary
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Catenary algebraic spaces

An algebraic space is catenary when every canonical topology on its points
is a catenary topological space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is catenary when every canonical topology on `|X|` is a
catenary space. -/
@[mk_iff]
class IsCatenary {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every canonical topology on `|X|` is a catenary space. -/
  catenarySpace :
    ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @CatenarySpace (Points X) τ

namespace IsCatenary

/-- A catenary algebraic space has catenary underlying point space in every
canonical topology. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsCatenary X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    @CatenarySpace (Points X) τ :=
  sorry

/-- Catenarity of every canonical topology on `|X|` witnesses `IsCatenary`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @CatenarySpace (Points X) τ) :
    IsCatenary X :=
  sorry

end IsCatenary

/-- A catenary scheme over `S`, viewed as an algebraic space, is catenary. -/
instance instIsCatenary_ofOver {S : Scheme.{u}} (U : Over S)
    [CatenarySpace U.left] : IsCatenary (ofOver U) :=
  sorry

/-- A scheme over `S`, viewed as an algebraic space, is catenary if and only if
the underlying scheme is a catenary space. -/
theorem isCatenary_ofOver_iff {S : Scheme.{u}} (U : Over S) :
    IsCatenary (ofOver U) ↔ CatenarySpace U.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
