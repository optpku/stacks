/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Filtered Complex Category

This module owns the category of cochain complexes in finite filtered objects and the concrete
bridges from termwise finite filtered complexes.  It keeps finiteness evidence at the object
boundary, so downstream constructions do not repeatedly rebuild full-subcategory witnesses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

namespace FilteredObject.Finite

/-- The category of cochain complexes whose terms carry finite filtrations. -/
@[stacks 05TW "finite filtered complex category"]
abbrev CochainComplex (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] :=
  _root_.CochainComplex (FilteredObject.Finite.category C) ℤ

namespace CochainComplex

/-- The inclusion from finite filtered complexes to all filtered complexes. -/
@[stacks 05TW "finite filtered complex inclusion"]
abbrev inclusion (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] :
    FilteredObject.Finite.CochainComplex C ⥤ FilteredComplex C :=
  (FilteredObject.Finite.inclusion C).mapHomologicalComplex (ComplexShape.up ℤ)

end CochainComplex
end FilteredObject.Finite

namespace FilteredComplex.Finite

/-- Regard a filtered complex with termwise finite filtrations as a complex in finite filtered
objects. -/
@[stacks 05TW "termwise finite filtered complex"]
def lift (K : FilteredComplex C) (hK : K.HasFiniteFiltrations) :
    FilteredObject.Finite.CochainComplex C :=
  { X n := ⟨K.X n, hK n⟩
    d i j := ObjectProperty.homMk (K.d i j)
    shape i j hij := by
      simp [K.shape i j hij]
    d_comp_d' i j k hij hjk := by
      ext
      simp [K.d_comp_d' i j k hij hjk] }

/-- Lift a map between termwise finite filtered complexes to a map in the finite filtered complex
category. -/
@[stacks 05TW "termwise finite filtered complex map"]
def liftMap {K L : FilteredComplex C} (hK : K.HasFiniteFiltrations)
    (hL : L.HasFiniteFiltrations) (f : K ⟶ L) :
    lift K hK ⟶ lift L hL :=
  { f n := ObjectProperty.homMk (f.f n)
    comm' i j hij := by
      ext
      exact f.comm' i j hij }

/-- Lift a map from a termwise finite filtered complex to a complex already presented in the
finite filtered complex category. -/
@[stacks 05TW "termwise finite filtered complex lift"]
def liftMapTo {K : FilteredComplex C} (hK : K.HasFiniteFiltrations)
    {L : FilteredObject.Finite.CochainComplex C}
    (f : K ⟶ (FilteredObject.Finite.CochainComplex.inclusion C).obj L) :
    lift K hK ⟶ L :=
  { f n := ObjectProperty.homMk (f.f n)
    comm' i j hij := by
      ext
      exact f.comm' i j hij }

namespace Lift

/-- Forgetting the finite presentation of a termwise finite filtered complex recovers the original
filtered complex. -/
@[simp, stacks 05TW "termwise finite filtered complex"]
theorem inclusion_obj (K : FilteredComplex C) (hK : K.HasFiniteFiltrations) :
    (FilteredObject.Finite.CochainComplex.inclusion C).obj (lift K hK) = K := sorry

/-- Forgetting a lifted map between termwise finite filtered complexes recovers the original map. -/
@[simp, stacks 05TW "termwise finite filtered complex map"]
theorem inclusion_map {K L : FilteredComplex C} (hK : K.HasFiniteFiltrations)
    (hL : L.HasFiniteFiltrations) (f : K ⟶ L) :
    (FilteredObject.Finite.CochainComplex.inclusion C).map (liftMap hK hL f) = f := sorry

/-- Forgetting a lift into an already finite filtered complex recovers its original comparison
map. -/
@[simp, stacks 05TW "termwise finite filtered complex lift"]
theorem inclusion_mapTo {K : FilteredComplex C} (hK : K.HasFiniteFiltrations)
    {L : FilteredObject.Finite.CochainComplex C}
    (f : K ⟶ (FilteredObject.Finite.CochainComplex.inclusion C).obj L) :
    (FilteredObject.Finite.CochainComplex.inclusion C).map (liftMapTo hK f) = f := sorry

/-- The lift of an identity map between termwise finite filtered complexes is the identity. -/
@[simp]
theorem map_id (K : FilteredComplex C) (hK : K.HasFiniteFiltrations) :
    liftMap hK hK (𝟙 K) = 𝟙 (lift K hK) := sorry

/-- Lifting maps between termwise finite filtered complexes respects composition. -/
@[simp]
theorem map_comp {K L M : FilteredComplex C} (hK : K.HasFiniteFiltrations)
    (hL : L.HasFiniteFiltrations) (hM : M.HasFiniteFiltrations)
    (f : K ⟶ L) (g : L ⟶ M) :
    liftMap hK hM (f ≫ g) = liftMap hK hL f ≫ liftMap hL hM g := sorry

end Lift

end FilteredComplex.Finite

end CategoryTheory
