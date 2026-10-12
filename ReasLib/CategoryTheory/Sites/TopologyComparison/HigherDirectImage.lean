/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Vanishing
public import ReasLib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Higher direct images under a topology comparison

This leaf relates degreewise direct images on two slice topologies.  The canonical bounded-below
map lives at `GrothendieckTopology.Derived.Plus.pushforwardComparison`; the statements here add
the coefficient property and local-vanishing hypotheses needed for its degreewise consequences.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.HigherDirectImage

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C} (hle : τ' ≤ τ)
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

section Vanishing

variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]

/-- Supporting vanishing bridge: `(V_n)` kills the positive derived topology-comparison direct
image of coefficients in `A_X` through degree `n`. -/
@[stacks 0EZA "supporting vanishing bridge"]
theorem comparisonPushforward_isZero
    (h : Situation τ τ' P A') (n : ℕ)
    (hVn : Situation.LocalVanishing h n) (X : C)
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : objectProperty hle A' X F) (i : ℕ) (hi₀ : 0 < i) (hi : i ≤ n) :
    IsZero (((comparisonTopologyPushforwardAb hle X).rightDerived i).obj F) := sorry

end Vanishing

section Comparison

variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]

/-- The cocontinuous-presentation companion of the source comparison statement.  The presentation
is canonically related to the continuous one by
`Derived.Over.pushforwardDegreePresentationIso`. -/
@[stacks 0EZA "cocontinuous presentation companion"]
theorem comparison_isomorphic_cocontinuous
    (h : Situation τ τ' P A') (n : ℕ)
    (hVn : Situation.LocalVanishing h n)
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    [∀ Q : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.map f).op.HasPointwiseRightKanExtension Q]
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : objectProperty hle A' X F) (i : ℕ) (hi : i ≤ n) :
    IsIsomorphic
      ((Derived.Over.pushforwardDegree τ' f i).obj
        ((comparisonTopologyPushforwardAb hle X).obj F))
      ((comparisonTopologyPushforwardAb hle Y).obj
        ((Derived.Over.pushforwardDegree τ f i).obj F)) := sorry

/-- Lemma 21.30.3 (0EZA): under `(V_n)`, the continuous degree-`i` direct image for the coarser
topology commutes with the topology-comparison direct image for every `i ≤ n`.  The pullback
certificate supplied by `Situation.hasPullbacks` and `hf` is used explicitly, so the statement
matches the source presentation `τ.overMapPushforward` without a hidden local instance. -/
@[stacks 0EZA]
theorem comparison_isomorphic
    (h : Situation τ τ' P A') (n : ℕ)
    (hVn : Situation.LocalVanishing h n)
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : objectProperty hle A' X F) (i : ℕ) (hi : i ≤ n) :
    IsIsomorphic
      ((Derived.Over.pushforwardDegreeContinuousOf τ' f i
        (MorphismProperty.HasPullbacks.hasPullbacksAlong_of_mem h.hasPullbacks hf)).obj
        ((comparisonTopologyPushforwardAb hle X).obj F))
      ((comparisonTopologyPushforwardAb hle Y).obj
        ((Derived.Over.pushforwardDegreeContinuousOf τ f i
          (MorphismProperty.HasPullbacks.hasPullbacksAlong_of_mem h.hasPullbacks hf)).obj F)) := sorry

end Comparison

section CanonicalComponent

variable {X Y : C} (f : X ⟶ Y)
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (g : X ⟶ Y),
  Functor.Additive
    ((Over.map g).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ'.over X) (τ'.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (τ.over X) (τ.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]
variable [Functor.HasRightDerivedFunctor
  ((comparisonTopologyPushforwardAb hle Y).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (τ.over Y) AddCommGrpCat.{max u v}))]

/-- The canonical degree component of the bounded-below comparison is invertible under the
source `(V_n)` certificate.  The map itself is owned by
`Derived.Plus.pushforwardComparisonHomologyAppOf`; this theorem supplies the reusable
invertibility fact without replacing that map by a proposition-level `IsIsomorphic` view. -/
@[stacks 0EZA "canonical homology component is invertible under (V_n)"]
theorem comparison_homology_isIso
    (h : Situation τ τ' P A') (n : ℕ)
    (hVn : Situation.LocalVanishing h n)
    (hf : P f)
    (F : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hF : objectProperty hle A' X F) (i : ℕ) (hi : i ≤ n) :
    IsIso
      (Derived.Plus.pushforwardComparisonHomologyAppOf hle f
        (MorphismProperty.HasPullbacks.hasPullbacksAlong_of_mem h.hasPullbacks hf)
        (i : ℤ) F) := sorry

end CanonicalComponent

end CategoryTheory.GrothendieckTopology.TopologyComparison.HigherDirectImage

end
