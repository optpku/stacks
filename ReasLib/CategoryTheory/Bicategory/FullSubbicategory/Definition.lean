module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Full subbicategories selected by object properties

This module contains only the object-property presentation, its canonical
inclusion, and the object constructor.  Equivalence lifting and strict
pseudofunctor lifts are available from focused sibling modules.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

/-- The full subbicategory of `D` selected by an object property `P`.

Its objects are the subtype `{X : D // P X}` and all ambient `1`- and `2`-morphisms are retained.
The definition reuses `Bicategory.InducedBicategory`; fullness is a property of the canonical
inclusion, not additional structure stored on the carrier. -/
abbrev FullSubbicategory (P : ObjectProperty D) :=
  Bicategory.InducedBicategory D (fun X : {X : D // P X} ↦ X.1)

namespace FullSubbicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Package an ambient object satisfying `P` as an object of the full subbicategory.
Using this constructor preserves the induced-bicategory owner during elaboration. -/
def mk (P : ObjectProperty D) (X : D) (hX : P X) : P.FullSubbicategory :=
  ⟨X, hX⟩

variable (P : ObjectProperty D)

/-- The canonical inclusion of a full subbicategory into its ambient bicategory. -/
def ι : StrictPseudofunctor P.FullSubbicategory D :=
  Bicategory.InducedBicategory.forget

/-- The canonical inclusion sends a full-subbicategory object to its ambient object. -/
@[simp]
theorem ι_obj (X : P.FullSubbicategory) :
    (ι P).obj X = X.1 := sorry

/-- The canonical inclusion sends a lifted `1`-morphism to its ambient representative. -/
@[simp]
theorem ι_map {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (ι P).map f = f.hom := sorry

/-- The canonical inclusion sends a lifted `2`-morphism to its ambient representative. -/
@[simp]
theorem ι_map₂ {X Y : P.FullSubbicategory} {f g : X ⟶ Y} (η : f ⟶ g) :
    (ι P).map₂ η = η.hom := sorry

end FullSubbicategory

end ObjectProperty

end CategoryTheory
