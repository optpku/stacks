module

public import stacks_project.Chap75.Lemma_75_7_3_ProperOver

/-!
# Finite unions of closed subsets proper over a base

A finite union of closed subsets of an algebraic space that are proper over a
base remains proper over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- A finite supremum of closed subsets proper over a base algebraic space is
proper over that base. -/
theorem IsProperOver.iSup {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {ι : Type v} [Finite ι] (T : ι → Closeds (Points X))
    (hproper : ∀ i, IsProperOver f (T i)) :
    IsProperOver f (iSup T) :=
  sorry

/-- The finite supremum of an inferred family of proper closed subsets is proper. -/
instance instIsProperOverISup {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {ι : Type v} [Finite ι]
    (T : ι → Closeds (Points X)) [∀ i, IsProperOver f (T i)] :
    IsProperOver f (iSup T) :=
  IsProperOver.iSup f T (fun i ↦ (inferInstance : IsProperOver f (T i)))

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
