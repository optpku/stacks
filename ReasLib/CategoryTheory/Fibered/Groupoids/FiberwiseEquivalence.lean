module

public import ReasLib.CategoryTheory.Fibered.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibrewise criteria for morphisms of categories fibred in groupoids

For morphisms of categories fibred in groupoids, faithfulness, full faithfulness, and equivalence
can all be checked fibrewise.  In this setting an equivalence of total categories also upgrades
canonically to an equivalence over the base.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

variable {X Y : FiberedCategoryOver.Groupoids C}
variable (F : X ⟶ Y)

/-- Lemma 4.35.9 (Stacks 003Z) (1): a morphism of categories fibred in groupoids is faithful
exactly when every induced fibre
functor is faithful. -/
@[stacks 003Z "(1) faithful iff fiberwise faithful"]
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔
      ∀ U : C, (fiberFunctor F U).Faithful := sorry
/- Proof strategy: apply the general `FiberedCategoryOver.faithful_iff_fiberwise` criterion to
the image of `F` under the canonical forgetful pseudofunctor to fibred categories. -/

/-- Lemma 4.35.9 (Stacks 003Z) (2): a morphism of categories fibred in groupoids is fully
faithful exactly when every induced
fibre functor is fully faithful. -/
@[stacks 003Z "(2) fully faithful iff fiberwise fully faithful"]
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := sorry
/- Proof strategy: apply the general `FiberedCategoryOver.fullyFaithful_iff_fiberwise` criterion
to the canonical forgetful morphism. -/

/-- Lemma 4.35.9 (Stacks 003Z) (3): a morphism of categories fibred in groupoids is an
equivalence on total categories exactly
when every induced fibre functor is an equivalence. -/
@[stacks 003Z "(3) total equivalence iff fiberwise equivalence"]
theorem isEquivalence_iff_fiberwise :
    (toFunctor F).IsEquivalence ↔
      ∀ U : C, (fiberFunctor F U).IsEquivalence := sorry
/- Proof strategy: the reverse direction follows from
`FiberedCategoryOver.exists_equivalence_of_fiberwise` after forgetting the resulting
bicategorical equivalence to total categories. Forward, use total full faithfulness and correct an
arbitrary total preimage into the required fibre by a cartesian lift of the base isomorphism; in
groupoid fibres that cartesian arrow is an isomorphism. -/

/-- Lemma 4.35.9 (Stacks 003Z) (4): an equivalence of the underlying total categories of a
morphism between categories fibred in
groupoids lifts to a bicategorical equivalence over `C` with the given forward `1`-morphism. -/
@[stacks 003Z "(4) lift total equivalence to an equivalence over the base"]
theorem toFunctor.existsEquivalence
    (hF : (toFunctor F).IsEquivalence) :
    ∃ e : X ≌ Y, e.hom = F := sorry
/- Proof strategy: use `isEquivalence_iff_fiberwise` to obtain fibrewise equivalences and apply
`FiberedCategoryOver.exists_equivalence_of_fiberwise` to the canonical forgetful morphism. -/

/-- Heterogeneous compatibility form of `toFunctor.existsEquivalence`. -/
theorem toFunctor.basedIsEquivalence
    (hF : (toFunctor F).IsEquivalence) :
    BasedFunctor.IsEquivalence (toBasedFunctor F) := sorry
/- Proof strategy: forget the bicategorical owner returned by
`toFunctor.existsEquivalence`, or apply the heterogeneous fiberwise compatibility theorem. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
