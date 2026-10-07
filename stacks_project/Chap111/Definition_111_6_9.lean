module

public import ReasLib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

universe spaceUniverse

/-
A nonempty topological space is irreducible when it cannot be written as a union of two proper
closed subsets. Mathlib owns this as `IrreducibleSpace`; the closed-union packaging is recovered
by `isPreirreducible_iff_isClosed_union_isClosed` together with nonempty. A subset `T` of `X` is
irreducible when the induced subspace is irreducible, i.e. `IsIrreducible T`, equivalently
`IrreducibleSpace` on `T` via `isIrreducible_iff_irreducibleSpace`. This implies `T` is
irreducible if and only if its closure in `X` is irreducible, which is `isIrreducible_iff_closure`.
-/

/- Definition 111.6.9 -/
@[stacks 027D]
#check (Topology.irreducibleSpace_iff_nonempty_closed_union :
  ∀ (space : Type spaceUniverse) [TopologicalSpace space],
    IrreducibleSpace space ↔
      Nonempty space ∧
        (∀ firstClosed secondClosed : Set space,
          IsClosed firstClosed →
            IsClosed secondClosed →
              firstClosed ∪ secondClosed = Set.univ →
                firstClosed = Set.univ ∨ secondClosed = Set.univ))

/- Canonical nonempty irreducibility class for topological spaces. -/
#check (IrreducibleSpace :
  ∀ (space : Type spaceUniverse) [TopologicalSpace space], Prop)

/- Closed-union packaging of the space-level definition, used together with nonempty. -/
#check (isPreirreducible_iff_isClosed_union_isClosed :
  ∀ {space : Type spaceUniverse} [TopologicalSpace space] {subset : Set space},
    IsPreirreducible subset ↔
      ∀ firstClosed secondClosed : Set space,
        IsClosed firstClosed → IsClosed secondClosed → subset ⊆ firstClosed ∪ secondClosed →
          subset ⊆ firstClosed ∨ subset ⊆ secondClosed)

/- Companion: `IrreducibleSpace X` is equivalent to irreducibility of `X` as a set. -/
#check (irreducibleSpace_def :
  ∀ (space : Type spaceUniverse) [TopologicalSpace space],
    IrreducibleSpace space ↔ IsIrreducible (⊤ : Set space))

/- A subset `T` of `X` is irreducible when it is irreducible in the induced topology. -/
#check (IsIrreducible :
  ∀ {space : Type spaceUniverse} [TopologicalSpace space], Set space → Prop)

/- Induced-topology wording of clause (2): `IsIrreducible T` iff `IrreducibleSpace` on `T`. -/
#check (isIrreducible_iff_irreducibleSpace :
  ∀ {space : Type spaceUniverse} [TopologicalSpace space] {subset : Set space},
    IsIrreducible subset ↔ IrreducibleSpace subset)

/- A subset `T` is irreducible if and only if its closure in `X` is irreducible. -/
#check (isIrreducible_iff_closure :
  ∀ {space : Type spaceUniverse} [TopologicalSpace space] {subset : Set space},
    IsIrreducible (closure subset) ↔ IsIrreducible subset)
