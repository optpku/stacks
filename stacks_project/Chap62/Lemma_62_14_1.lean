/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_14_1_Comp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Well-definedness of composition of relative cycles

This file records that composition of fibre-cycle families preserves the
relative-cycle condition, inducing a bilinear map on the groups `z(X/Y, r)`
and `z(Y/S, e)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.14.1: if `α` is a relative `r`-cycle on `X / Y` and `β` is a
relative `e`-cycle on `Y / S`, with `S` locally Noetherian and `X ⟶ Y ⟶ S`
locally of finite type, then the composite family `comp α β` is a relative
`(r + e)`-cycle on `X / S`. -/
@[stacks 0H6R]
theorem isRelative_comp {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : Family f r) (β : Family p e) (hα : IsRelative α) (hβ : IsRelative β) :
    IsRelative (comp α β) := sorry

/-- The composite of relative cycles lies in `z(X/S, r + e)`. -/
theorem comp_mem_group {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : Family f r) (β : Family p e) (hα : IsRelative α) (hβ : IsRelative β) :
    comp α β ∈ group (f ≫ p) (r + e) := sorry

/-- The bilinear composition map
`z(X/Y, r) →+ z(Y/S, e) →+ z(X/S, r + e)`. -/
noncomputable def groupComp {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] (r e : ℕ) :
    group f r →+ group p e →+ group (f ≫ p) (r + e) where
  toFun α :=
    { toFun β :=
        ⟨comp (α : Family f r) (β : Family p e),
          comp_mem_group p f (α : Family f r) (β : Family p e)
            α.property β.property⟩
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

/-- The underlying fibrewise family of `groupComp` is family-level `comp`. -/
theorem groupComp_apply {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : group f r) (β : group p e) :
    (groupComp p f r e α β : Family (f ≫ p) (r + e)) =
      comp (α : Family f r) (β : Family p e) := sorry

end AlgebraicGeometry.RelativeCycle

