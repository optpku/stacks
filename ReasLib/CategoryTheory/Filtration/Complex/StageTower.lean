/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The integer tower of filtration stages

A filtered cochain complex determines a diagram indexed by `ℤᵒᵖ`.  This file owns that
construction before passing to a derived category, together with its canonical cocone and its
functoriality in the filtered complex.
-/

open CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.StageTower

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The identity law for the integer tower of filtration stages. -/
@[simp, stacks 012L "identity law for the integer filtration-stage tower"]
theorem diagram_map_id (K : FilteredComplex C) (i : ℤᵒᵖ) :
    K.stageComparison (le_refl i.unop) = 𝟙 (K.stage i.unop) := sorry

/-- The composition law for the integer tower of filtration stages. -/
@[simp, stacks 012L "composition law for the integer filtration-stage tower"]
theorem diagram_map_comp (K : FilteredComplex C) {i j k : ℤᵒᵖ}
    (f : i ⟶ j) (g : j ⟶ k) :
    K.stageComparison (f ≫ g).unop.le =
      K.stageComparison f.unop.le ≫ K.stageComparison g.unop.le := sorry

/-- The `ℤᵒᵖ`-indexed diagram formed by all filtration stages of `K`. -/
@[stacks 012L "integer filtration-stage tower"]
def diagram (K : FilteredComplex C) : ℤᵒᵖ ⥤ CochainComplex C ℤ where
  obj i := K.stage i.unop
  map f := K.stageComparison f.unop.le
  map_id i := diagram_map_id K i
  map_comp f g := diagram_map_comp K f g

/-- Evaluating the integer stage tower at `i` gives the `i.unop`-th filtration stage. -/
@[simp]
theorem diagram_obj (K : FilteredComplex C) (i : ℤᵒᵖ) :
    (diagram K).obj i = K.stage i.unop := sorry

/-- Maps in the integer stage tower are the canonical stage comparisons. -/
@[simp]
theorem diagram_map (K : FilteredComplex C) {i j : ℤᵒᵖ} (f : i ⟶ j) :
    (diagram K).map f = K.stageComparison f.unop.le := sorry

/-- Naturality of the filtration-stage inclusions into the underlying complex. -/
@[reassoc]
theorem toUnderlying_naturality (K : FilteredComplex C) {i j : ℤᵒᵖ}
    (f : i ⟶ j) :
    (diagram K).map f ≫ K.stageInclusion j.unop =
      K.stageInclusion i.unop ≫ ((Functor.const ℤᵒᵖ).obj K.underlying).map f := sorry

/-- The natural transformation from the stage tower to the constant underlying complex. -/
@[stacks 012L "integer filtration-stage inclusions"]
def toUnderlying (K : FilteredComplex C) :
    diagram K ⟶ (Functor.const ℤᵒᵖ).obj K.underlying where
  app i := K.stageInclusion i.unop
  naturality := fun _ _ f ↦ toUnderlying_naturality K f

/-- A component of `toUnderlying` is the corresponding stage inclusion. -/
@[simp]
theorem toUnderlying_app (K : FilteredComplex C) (i : ℤᵒᵖ) :
    (toUnderlying K).app i = K.stageInclusion i.unop := sorry

/-- The canonical cocone from the integer stage tower to the underlying complex. -/
@[stacks 012L "integer filtration-stage cocone"]
def cocone (K : FilteredComplex C) : Cocone (diagram K) :=
  Cocone.mk K.underlying (toUnderlying K)

/-- The point of the integer stage-tower cocone is the underlying cochain complex. -/
@[simp, stacks 012L "point of the integer filtration-stage cocone"]
theorem cocone_pt (K : FilteredComplex C) :
    (cocone K).pt = K.underlying := sorry

/-- The legs of the integer stage-tower cocone are the canonical stage inclusions. -/
@[simp, stacks 012L "legs of the integer filtration-stage cocone"]
theorem cocone_ι_app (K : FilteredComplex C) (i : ℤᵒᵖ) :
    (cocone K).ι.app i = K.stageInclusion i.unop := sorry

/-- A filtered morphism commutes with the maps in the integer stage towers. -/
@[reassoc]
theorem map_naturality {K L : FilteredComplex C} (f : K ⟶ L)
    {i j : ℤᵒᵖ} (g : i ⟶ j) :
    (diagram K).map g ≫ K.stageMap f j.unop =
      K.stageMap f i.unop ≫ (diagram L).map g := sorry

/-- A filtered morphism induces a natural transformation of integer stage towers. -/
@[stacks 012L "map of integer filtration-stage towers"]
def map {K L : FilteredComplex C} (f : K ⟶ L) : diagram K ⟶ diagram L where
  app i := K.stageMap f i.unop
  naturality := fun _ _ g ↦ map_naturality f g

/-- A component of the induced tower map is the corresponding filtration-stage map. -/
@[simp]
theorem map_app {K L : FilteredComplex C} (f : K ⟶ L) (i : ℤᵒᵖ) :
    (map f).app i = K.stageMap f i.unop := sorry

/-- The tower map induced by an identity is the identity natural transformation. -/
@[simp]
theorem map_id (K : FilteredComplex C) : map (𝟙 K) = 𝟙 (diagram K) := sorry

/-- Passage to integer stage towers preserves composition. -/
@[simp]
theorem map_comp {K L M : FilteredComplex C} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Taking the integer tower of filtration stages is functorial in the filtered complex. -/
@[stacks 012L "integer filtration-stage tower functor"]
def functor : FilteredComplex C ⥤ (ℤᵒᵖ ⥤ CochainComplex C ℤ) where
  obj K := diagram K
  map f := map f
  map_id K := map_id K
  map_comp f g := map_comp f g

/-- The object of the integer stage-tower functor is the corresponding diagram. -/
@[simp, stacks 012L "object of the integer filtration-stage tower functor"]
theorem functor_obj (K : FilteredComplex C) :
    (functor (C := C)).obj K = diagram K := sorry

/-- The map of the integer stage-tower functor is the induced tower map. -/
@[simp, stacks 012L "map of the integer filtration-stage tower functor"]
theorem functor_map {K L : FilteredComplex C} (f : K ⟶ L) :
    (functor (C := C)).map f = map f := sorry

/-- Tower maps and underlying maps commute with the canonical stage inclusions. -/
@[reassoc]
theorem map_comp_toUnderlying {K L : FilteredComplex C} (f : K ⟶ L) :
    map f ≫ toUnderlying L =
      toUnderlying K ≫ (Functor.const ℤᵒᵖ).map (K.underlyingMap f) := sorry

end CategoryTheory.FilteredComplex.StageTower
