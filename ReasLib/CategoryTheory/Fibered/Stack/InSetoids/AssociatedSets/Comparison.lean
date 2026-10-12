/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Naturality
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with the associated stack in sets

This leaf owns the choice-free comparison from a stack in setoids to the setoid view of its
associated stack in sets.  Its bundled naturality is a thin lift of the neutral comparison, and
the pointwise `hom.app`/`inv.app` readouts are retained for downstream rewriting.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type uC} [Category.{vC} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

/-- The canonical comparison from a stack in setoids to the setoid-stack view of its associated
stack in sets. -/
@[stacks 0432 "comparison with associated stack in sets"]
noncomputable def toAssociatedSets (X : StackOver.Setoids J) :
    X ⟶ X.associatedSets.toSetoids :=
  StackOver.Setoids.Hom.ofSetoidsMor
    (FiberedCategoryOver.Setoids.toAssociatedSets X.toSetoids)

namespace toAssociatedSets

/-- Forgetting the stack wrapper from the associated-sets comparison recovers the canonical
comparison of categories fibred in setoids. -/
@[simp, stacks 0432 "underlying associated-sets comparison"]
theorem toSetoidsMor (X : StackOver.Setoids J) :
    StackOver.Setoids.Hom.toSetoidsMor X.toAssociatedSets =
      FiberedCategoryOver.Setoids.toAssociatedSets X.toSetoids := sorry

/-- The associated-sets comparison is natural at the bundled stack level.  The underlying
setoid-fibred naturality is lifted through the canonical full-subbicategory Hom owner, so no
representatives of fibrewise isomorphism classes or auxiliary stack morphism are chosen. -/
@[stacks 0432 "bundled associated-sets naturality"]
noncomputable def naturalityIso {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    X.toAssociatedSets ≫
        StackOver.Sets.Hom.toSetoidsMor (associatedSets.map F) ≅
      F ≫ Y.toAssociatedSets :=
  StackOver.Setoids.Hom.isoMk
    (Bicategory.InducedBicategory.isoMk
      (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
        (FiberedCategoryOver.Setoids.toBasedFunctorIso
          (FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso
            (StackOver.Setoids.Hom.toSetoidsMor F)))))

namespace naturalityIso

/-- The forward object component of bundled associated-sets naturality is the canonical neutral
category-of-elements component. -/
@[simp, stacks 0432 "bundled associated-sets naturality forward component"]
theorem hom.app {X Y : StackOver.Setoids J} (F : X ⟶ Y) (x : X.total) :
    (StackOver.Setoids.Hom.toBasedFunctorIso
      (toAssociatedSets.naturalityIso F)).hom.toNatTrans.app x =
        (FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso.component
          (StackOver.Setoids.Hom.toSetoidsMor F) x).hom := sorry

/-- The inverse object component of bundled associated-sets naturality is the inverse canonical
neutral category-of-elements component. -/
@[simp, stacks 0432 "bundled associated-sets naturality inverse component"]
theorem inv.app {X Y : StackOver.Setoids J} (F : X ⟶ Y) (x : X.total) :
    (StackOver.Setoids.Hom.toBasedFunctorIso
      (toAssociatedSets.naturalityIso F)).inv.toNatTrans.app x =
        (FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso.component
          (StackOver.Setoids.Hom.toSetoidsMor F) x).inv := sorry

end naturalityIso

/-- The comparison with associated sets is an equivalence over the base. -/
@[stacks 0432 "associated-sets comparison equivalence"]
instance isEquivalence (X : StackOver.Setoids J) :
    StackOver.Setoids.Hom.IsEquivalence X.toAssociatedSets := sorry

end toAssociatedSets

/- Data audit: `toAssociatedSets` is the choice-free comparison sending an object to its
fiberwise isomorphism class.  Its bundled naturality is lifted from the neutral
`FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso`; no inverse morphism is packaged
here because constructing one would require choosing a representative of every isomorphism
class. -/

end StackOver.Setoids

end CategoryTheory
