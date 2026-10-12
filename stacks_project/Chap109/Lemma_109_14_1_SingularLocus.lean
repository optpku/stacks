/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_37_9_SourceLocus

/-!
# Isolated singularities of morphisms of algebraic spaces

The nonsmooth locus of a morphism of algebraic spaces is the closed complement of
the smooth source locus. The morphism has isolated singularities when this locus,
with its reduced induced closed subspace structure, is finite over the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of points of the source at which a morphism of algebraic spaces is
not smooth. -/
def nonsmoothLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  (Smooth.sourceLocus f).pointsSetᶜ

/-- A point lies in the nonsmooth locus if and only if the morphism is not
smooth at that point. -/
theorem mem_nonsmoothLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {x : Points X} :
    x ∈ nonsmoothLocus f ↔ ¬ SmoothAt f x :=
  sorry

/-- The nonsmooth locus is the set of points at which the morphism is not
smooth. -/
theorem nonsmoothLocus_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    nonsmoothLocus f = setOf fun x ↦ ¬ SmoothAt f x :=
  sorry

/-- The nonsmooth locus as a closed subset of the space of points of the
source. -/
def nonsmoothLocusClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Closeds (Points X) :=
  Opens.compl (Smooth.sourceLocus f).pointsOpens

/-- The carrier of `nonsmoothLocusClosed f` is `nonsmoothLocus f`. -/
theorem nonsmoothLocusClosed_carrier {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (nonsmoothLocusClosed f).carrier = nonsmoothLocus f :=
  sorry

/-- A morphism of algebraic spaces has isolated singularities if the nonsmooth
locus, endowed with its reduced induced closed subspace structure, is finite
over the target. -/
class IsolatedSingularities {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The reduced induced structure on the nonsmooth locus is finite over the
  target. -/
  isFinite_reduced :
    IsFinite ((ClosedSubspaceStructure.reduced (nonsmoothLocusClosed f)).ι ≫ f)

/-- A smooth morphism of algebraic spaces has isolated singularities. -/
instance instIsolatedSingularities_of_smooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f] :
    IsolatedSingularities f :=
  sorry

/-- Isolated singularities is equivalent to finiteness of the reduced induced
structure on the nonsmooth locus. -/
theorem isolatedSingularities_isFinite_reduced {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsolatedSingularities f] :
    IsFinite ((ClosedSubspaceStructure.reduced (nonsmoothLocusClosed f)).ι ≫ f) :=
  sorry

/-- For a proper morphism, isolated singularities is equivalent to every closed
subspace structure on the nonsmooth locus being finite over the target. -/
theorem isolatedSingularities_iff_forall {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] :
    IsolatedSingularities f ↔
      ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed f),
        IsFinite (T.ι ≫ f) :=
  sorry

/-- Isolated singularities is equivalent to some closed subspace structure on
the nonsmooth locus being finite over the target. -/
theorem isolatedSingularities_iff_exists {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsolatedSingularities f ↔
      ∃ T : ClosedSubspaceStructure (nonsmoothLocusClosed f),
        IsFinite (T.ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
