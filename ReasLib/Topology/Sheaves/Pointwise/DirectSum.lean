/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Pointwise direct-sum presheaves

For a family of abelian groups on the points of a topological space, this file constructs the
presheaf whose sections are finitely supported dependent functions. Restriction to a smaller open
discards coordinates outside that open.

## API under `TopCat.Presheaf.PointwiseDirectSum`

- `section'` — the type of sections on an open (finitely-supported dependent functions)
- `restrictMap` — restriction along an inclusion of opens
- `presheaf` — the ambient presheaf
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v

namespace TopCat.Presheaf.PointwiseDirectSum

variable {X : TopCat.{u}} (M : X → Type v) [∀ x, AddCommGroup (M x)]

/-- Sections of the pointwise direct-sum presheaf on an open set. -/
abbrev section' (U : Opens X) : Type max u v :=
  Π₀ x : U, M x.1

/-- Restrict a direct-sum section along an inclusion of opens. -/
noncomputable abbrev restrictMap {U V : Opens X} (i : V ⟶ U) :
    section' M U →+ section' M V :=
  AddMonoidHom.mk'
    (DFinsupp.comapDomain (Opens.inclusion i.le) (Set.inclusion_injective i.le))
    (DFinsupp.comapDomain_add (Opens.inclusion i.le) (Set.inclusion_injective i.le))

/-- Restricting along the identity is the identity. -/
theorem restrictMap_id (U : Opens X) :
    restrictMap M (𝟙 U) = AddMonoidHom.id _ := sorry

/-- Successive restrictions agree with restriction along the composite. -/
theorem restrictMap_comp {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) :
    restrictMap M (j ≫ i) =
      (restrictMap M j).comp (restrictMap M i) := sorry

/-- The presheaf of pointwise direct sums. -/
@[stacks 006L "presheaf of pointwise direct sums of abelian groups"]
noncomputable abbrev presheaf : X.Presheaf AddCommGrpCat.{max u v} where
  obj U := AddCommGrpCat.of (section' M U.unop)
  map {_ _} i := AddCommGrpCat.ofHom (restrictMap M i.unop)
  map_id U := congrArg AddCommGrpCat.ofHom (restrictMap_id M U.unop)
  map_comp i j := congrArg AddCommGrpCat.ofHom (restrictMap_comp M i.unop j.unop)

/-- Restriction keeps the coordinate at each point of the smaller open. -/
@[simp]
theorem presheaf_map_apply {U V : Opens X} (i : V ⟶ U)
    (s : Π₀ x : U, M x.1) (y : V) :
    ((presheaf M).map i.op s) y = s ⟨y, i.le y.2⟩ := sorry

/-- On an infinite discrete space, a pointwise direct-sum presheaf with nontrivial fibers is not
a sheaf: gluing nonzero singleton sections would produce a section with infinite support. -/
theorem not_isSheaf_of_infinite_discrete [DiscreteTopology X] [Infinite X]
    [∀ x, Nontrivial (M x)] :
    ¬ (presheaf M).IsSheaf := sorry

/-- If every open subset of `X` is compact, then the pointwise direct-sum presheaf is a sheaf. -/
theorem isSheaf_of_compact_opens (hqc : ∀ U : Opens X, IsCompact (U : Set X)) :
    (presheaf M).IsSheaf := sorry

end TopCat.Presheaf.PointwiseDirectSum

end

end
