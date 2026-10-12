/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver

/-!
# Properness over a base for closed subsets of algebraic spaces

Properness of a closed subset along a locally of finite type morphism of algebraic
spaces is equivalent for the reduced induced structure, for some closed-subspace
structure, and for every closed-subspace structure with the same underlying point-set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- Properness of a closed subset over a base is equivalent to properness of the
reduced induced structure, of some closed-subspace structure, and of every
closed-subspace structure with the same underlying closed subset. -/
theorem isProperOver_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    List.TFAE [
      IsProperOver f T,
      ∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f),
      ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f)] :=
  sorry

/-- A closed subset is proper over a base if and only if some closed-subspace
structure on it is proper over that base. -/
theorem isProperOver_iff_exists {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    IsProperOver f T ↔ ∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  sorry

/-- A closed subset is proper over a base if and only if every closed-subspace
structure on it is proper over that base. -/
theorem isProperOver_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    IsProperOver f T ↔ ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  sorry

/-- Some closed-subspace structure on a closed subset is proper over a base if and
only if every such structure is proper over that base. -/
theorem isProperOver_exists_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    (∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f)) ↔
      ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
