module

public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.2. For any family `S0` of schemes there exists a small object property `P` of
schemes containing every `S0 i`, such that whenever `P S` and `T.size ≤ bound S.size` the
scheme `T` is isomorphic to a member of `P`, and such that a countable diagram in
`P.FullSubcategory` has a (co)limit if and only if the composite with `P.ι` has a (co)limit
in `Scheme`, in which case the canonical comparison `limit.post` (resp. `colimit.post`) is an
isomorphism.

The Stacks Project packages this as a limit ordinal `α` with `Sch_α` the full subcategory of
schemes lying in `V_α`; Lean records the same closure and comparison properties on a small
`ObjectProperty` of `Scheme`. -/
@[stacks 000J]
theorem exists_isSmallBoundClosed {ι : Type u} (S0 : ι → Scheme.{u}) :
    ∃ P : ObjectProperty Scheme.{u},
      IsSmallBoundClosed P ∧ ObjectProperty.ofObj S0 ≤ P := sorry

end AlgebraicGeometry.Scheme
