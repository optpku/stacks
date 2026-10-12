/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Category.Factorisation.Composition

@[expose] public section

/-!
# Morphisms factoring through an object property

The Type-valued `ObjectProperty.Factorisation` retains the chosen midpoint and maps.  The
MorphismProperty-valued `ObjectProperty.factorThru` records only existence and is stable under
arbitrary pre- and postcomposition.
@stack 0G90
-/

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]
variable (P Q : ObjectProperty C)
variable {W X Y Z : C} {f : X ⟶ Y}

/-- A factorisation of `f` whose midpoint satisfies `P`. -/
structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The underlying categorical factorisation. -/
  base : CategoryTheory.Factorisation f
  /-- The object property at the selected midpoint. -/
  mem : P base.mid

namespace Factorisation

/-- Precompose a factorisation through `P` while retaining its midpoint. -/
def precomp (F : P.Factorisation f) (e : W ⟶ X) : P.Factorisation (e ≫ f) where
  base := F.base.precomp e
  mem := F.mem

/-- Postcompose a factorisation through `P` while retaining its midpoint. -/
def postcomp (F : P.Factorisation f) (e : Y ⟶ Z) : P.Factorisation (f ≫ e) where
  base := F.base.postcomp e
  mem := F.mem

/-- Enlarge the property satisfied by the midpoint of a factorisation. -/
def map {P Q : ObjectProperty C} (h : P ≤ Q) (F : P.Factorisation f) : Q.Factorisation f where
  base := F.base
  mem := h _ F.mem

end Factorisation

/-- The morphism property of maps admitting a factorisation through an object satisfying `P`. -/
@[stacks 0G90 "factorisation through an object property"]
def factorThru : MorphismProperty C :=
  fun _ _ f ↦ Nonempty (P.Factorisation f)

/-- Factoring through a smaller object property implies factoring through a larger one. -/
theorem factorThru_mono {P Q : ObjectProperty C} (h : P ≤ Q) :
    P.factorThru ≤ Q.factorThru := sorry

/-- Factorisation through an object property is stable under arbitrary precomposition. -/
instance factorThru_respectsLeft :
    P.factorThru.RespectsLeft (⊤ : MorphismProperty C) := sorry

/-- Factorisation through an object property is stable under arbitrary postcomposition. -/
instance factorThru_respectsRight :
    P.factorThru.RespectsRight (⊤ : MorphismProperty C) := sorry

/-- Explicit precomposition API for factorisation through an object property. -/
theorem factorThru_precomp (hf : P.factorThru f) (e : W ⟶ X) :
    P.factorThru (e ≫ f) := sorry

/-- Explicit postcomposition API for factorisation through an object property. -/
theorem factorThru_postcomp (hf : P.factorThru f) (e : Y ⟶ Z) :
    P.factorThru (f ≫ e) := sorry

/-- Simultaneous pre- and postcomposition preserves factorisation through `P`. -/
theorem factorThru_comp (hf : P.factorThru f) (e : W ⟶ X) (g : Y ⟶ Z) :
    P.factorThru (e ≫ f ≫ g) := sorry

end CategoryTheory.ObjectProperty
