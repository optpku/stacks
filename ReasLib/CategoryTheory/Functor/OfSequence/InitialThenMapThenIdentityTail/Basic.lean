/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic Stabilizing Sequential Diagrams of a Morphism

For a morphism `u : X ⟶ Y` in a category with an initial object, this leaf
owns the standard sequential presentation

```text
⊥ ⟶ X ⟶ Y ⟶ Y ⟶ ⋯.
```

The construction is deliberately phrased using the initial object rather than
a zero morphism, so it applies outside pointed and preadditive categories.
The `Map` leaf adds functoriality under commutative squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor.InitialThenMapThenIdentityTail

variable {C : Type u} [Category.{v} C] [HasInitial C]

noncomputable section

/-- The stages of the sequential diagram `⊥ ⟶ X ⟶ Y ⟶ Y ⟶ ⋯` associated to a morphism
`X ⟶ Y`. -/
abbrev stage (X Y : C) : ℕ → C
  | 0 => ⊥_ C
  | 1 => X
  | _ + 2 => Y

/-- The successor maps of the sequential diagram `⊥ ⟶ X ⟶ Y ⟶ Y ⟶ ⋯` associated to `u`. -/
abbrev step {X Y : C} (u : X ⟶ Y) :
    ∀ n : ℕ, stage X Y n ⟶ stage X Y (n + 1)
  | 0 => initial.to X
  | 1 => u
  | _ + 2 => 𝟙 Y

/-- The standard stabilizing sequential diagram associated to a morphism `u : X ⟶ Y`. -/
abbrev diagram {X Y : C} (u : X ⟶ Y) : ℕ ⥤ C :=
  Functor.ofSequence (step u)

/-- The zeroth stage of the stabilizing sequential diagram is the initial object. -/
@[simp]
theorem stage_zero (X Y : C) : stage X Y 0 = ⊥_ C := sorry

/-- The first noninitial stage of the stabilizing sequential diagram is `X`. -/
@[simp]
theorem stage_one (X Y : C) : stage X Y 1 = X := sorry

/-- Every stage from index `2` onward is `Y`. -/
@[simp]
theorem stage_tail (X Y : C) (n : ℕ) : stage X Y (n + 2) = Y := sorry

/-- The first successor map of the stabilizing sequential diagram is the unique map from the
initial object to `X`. -/
@[simp]
theorem step_zero {X Y : C} (u : X ⟶ Y) : step u 0 = initial.to X := sorry

/-- In a category with zero morphisms, the first successor map of the stabilizing diagram is the
zero morphism. -/
@[simp]
theorem step_zero_eq_zero [HasZeroMorphisms C] {X Y : C} (u : X ⟶ Y) :
    step u 0 = 0 := sorry

/-- The second successor map of the stabilizing sequential diagram is the input morphism. -/
@[simp]
theorem step_one {X Y : C} (u : X ⟶ Y) : step u 1 = u := sorry

/-- Every successor map from index `2` onward is the identity of `Y`. -/
@[simp]
theorem step_tail {X Y : C} (u : X ⟶ Y) (n : ℕ) : step u (n + 2) = 𝟙 Y := sorry

/-- The successor map in the diagram is its specified sequence step. -/
@[simp]
theorem diagram_map_succ {X Y : C} (u : X ⟶ Y) (n : ℕ) :
    (diagram u).map (homOfLE (Nat.le_succ n)) = step u n := sorry

/-- Every transition entirely inside the `Y` tail of the stabilizing diagram is the identity. -/
theorem diagram_map_tail {X Y : C} (u : X ⟶ Y) {m n : ℕ} (hmn : m ≤ n) :
    (diagram u).map
        (homOfLE (Nat.succ_le_succ (Nat.succ_le_succ hmn))) =
      𝟙 Y := sorry

/-- The standard stabilizing diagram is eventually constant from its `Y` stage. -/
theorem isEventuallyConstantFrom_two {X Y : C} (u : X ⟶ Y) :
    (diagram u).IsEventuallyConstantFrom 2 := sorry

/-- A stabilizing sequential diagram admits a colimit, supplied by its eventually constant
tail. Use this theorem as a local instance when an explicit colimit object is needed. -/
theorem hasColimit {X Y : C} (u : X ⟶ Y) : HasColimit (diagram u) := sorry

/-- The canonical comparison from `Y` to a chosen colimit of its stabilizing sequential diagram.
The eventual-constancy certificate is explicit so the data owner is independent of any particular
proof of tail constancy. -/
noncomputable def colimitIso {X Y : C} (u : X ⟶ Y)
    (h : (diagram u).IsEventuallyConstantFrom 2) [HasColimit (diagram u)] :
    Y ≅ colimit (diagram u) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.isColimitCocone).symm

end

end CategoryTheory.Functor.InitialThenMapThenIdentityTail
