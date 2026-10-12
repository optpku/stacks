/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Equivalence
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded derived restrictions for a topology comparison

This leaf owns the coefficient subcategories and the two bounded-below derived functors appearing
in Lemma 21.30.9.  The long source-facing names remain available in the chapter recall block; new
code should use the short names in `TopologyComparison.Restriction`.
-/

open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open DerivedCategory
open scoped CategoryTheory.GrothendieckTopology DerivedCategory.CohomologyIn

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.Restriction

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable (hle : τ' ≤ τ)
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

section WeakSerre

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]

/-- The certificate-dependent core of the weak-Serre transfer. -/
@[stacks 0EZG "weak-Serre transfer from an all-degree certificate"]
theorem objectProperty_isWeakSerre_of_allVanishing
    (h : Situation τ τ' P A') (hV : Situation.AllVanishing h) (X : C) :
    IsWeakSerreClass (objectProperty hle A' X) := sorry

/-- Lemma 21.30.9 (0EZG): the pulled-back coefficient property is weak Serre.  The
all-degree certificate is a consequence of the surrounding Situation hypotheses (0EZF). -/
@[stacks 0EZG]
theorem objectProperty_isWeakSerre
    (h : Situation τ τ' P A') (X : C) :
    IsWeakSerreClass (objectProperty hle A' X) := sorry

end WeakSerre

section Pullback

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]

/-- The exact inverse image carries the selected bounded-below cohomology range to `A_X`. -/
@[stacks 0EZG "bounded-below inverse-image coefficient range"]
theorem pullback_mapsTo
    (h : Situation τ τ' P A') (X : C) :
    Plus.cohomologyIn (A' X) ≤
      (Plus.cohomologyIn (objectProperty hle A' X)).inverseImage
        (Derived.Plus.pullback hle X) := sorry

/-- Objectwise membership form of `pullback_mapsTo`. -/
@[stacks 0EZG "objectwise bounded-below inverse-image coefficient range"]
theorem pullback_obj_mem
    (h : Situation τ τ' P A') (X : C) (K : D⁺[A' X]) :
    Plus.cohomologyIn (objectProperty hle A' X)
      ((Derived.Plus.pullback hle X).obj K.obj) := sorry

/-- The bounded-below inverse image restricted to the selected coefficient subcategories. -/
@[stacks 0EZG "restricted bounded-below inverse image"]
noncomputable def pullback
    (h : Situation τ τ' P A') (X : C) :
    D⁺[A' X] ⥤ D⁺[objectProperty hle A' X] :=
  FullSubcategory.restrict (Derived.Plus.pullback hle X)
    (pullback_mapsTo hle h X)

end Pullback

section Pushforward

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- The bounded-below right-derived direct image carries `A_X` into `A'_X`. -/
@[stacks 0EZG "bounded-below direct-image coefficient range"]
theorem pushforward_mapsTo
    (h : Situation τ τ' P A') (X : C) :
    Plus.cohomologyIn (objectProperty hle A' X) ≤
      (Plus.cohomologyIn (A' X)).inverseImage
        (Derived.Plus.pushforward hle X) := sorry

/-- Objectwise membership form of `pushforward_mapsTo`. -/
@[stacks 0EZG "objectwise bounded-below direct-image coefficient range"]
theorem pushforward_obj_mem
    (h : Situation τ τ' P A') (X : C) (K : D⁺[objectProperty hle A' X]) :
    Plus.cohomologyIn (A' X)
      ((Derived.Plus.pushforward hle X).obj K.obj) := sorry

/-- The bounded-below right-derived direct image restricted to the selected coefficient subcategories. -/
@[stacks 0EZG "restricted bounded-below direct image"]
noncomputable def pushforward
    (h : Situation τ τ' P A') (X : C) :
    D⁺[objectProperty hle A' X] ⥤ D⁺[A' X] :=
  FullSubcategory.restrict (Derived.Plus.pushforward hle X)
    (pushforward_mapsTo hle h X)

end Pushforward

section Equivalence

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- The certificate-dependent core of the restricted direct-image equivalence. -/
@[stacks 0EZG "restricted direct-image equivalence from an all-degree certificate"]
theorem pushforward_isEquivalence_of_allVanishing
    (h : Situation τ τ' P A') (hV : Situation.AllVanishing h) (X : C) :
    Functor.IsEquivalence (pushforward hle h X) := sorry

/-- Lemma 21.30.9 (0EZG): the restricted direct image is an equivalence.  The all-degree
certificate is obtained from the Situation by Lemma 21.30.8 (0EZF). -/
@[stacks 0EZG]
theorem pushforward_isEquivalence
    (h : Situation τ τ' P A') (X : C) :
    Functor.IsEquivalence (pushforward hle h X) := sorry

/-- The certificate-dependent core of the restricted inverse-image equivalence. -/
@[stacks 0EZG "restricted inverse-image equivalence from an all-degree certificate"]
theorem pullback_isEquivalence_of_allVanishing
    (h : Situation τ τ' P A') (hV : Situation.AllVanishing h) (X : C) :
    Functor.IsEquivalence (pullback hle h X) := sorry

/-- Lemma 21.30.9 (0EZG): the restricted inverse image is the quasi-inverse equivalence. -/
@[stacks 0EZG "restricted inverse-image equivalence"]
theorem pullback_isEquivalence
    (h : Situation τ τ' P A') (X : C) :
    Functor.IsEquivalence (pullback hle h X) := sorry

end Equivalence

end CategoryTheory.GrothendieckTopology.TopologyComparison.Restriction

end
