/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Lemma_62_8_3_RelativeCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

/-- Effectiveness of a family of fibre cycles is preserved by flat pullback along a
morphism of relative dimension `e`. -/
theorem IsEffective.flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} {α : CyclesOnFibers f r} (hα : α.IsEffective)
    (h : X' ⟶ X) (e : ℕ) [Flat h] [RelativeDimension h e] :
    (α.flatPullback h e).IsEffective := sorry

/-- Lemma 62.8.5: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r, e ≥ 0` be integers. Let `α`
be a relative `r`-cycle on `X / S`. Let `{f_i : X_i ⟶ X}` be a jointly
surjective family of flat morphisms, locally of finite type, and of relative
dimension `e`. Then `α` is effective if and only if each flat pullback
`f_i^* α` is effective. -/
@[stacks 0H5V]
theorem isEffective_iff_forall_flatPullback {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α) :
    α.IsEffective ↔ ∀ i, (α.flatPullback (family i).hom e).IsEffective := sorry

/-- If every flat pullback of a relative `r`-cycle along a jointly surjective
family of flat morphisms of relative dimension `e` is effective, then the
relative cycle is effective. -/
theorem isEffective_of_forall_flatPullback {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    (h_eff : ∀ i, (α.flatPullback (family i).hom e).IsEffective) :
    α.IsEffective := sorry

end AlgebraicGeometry
