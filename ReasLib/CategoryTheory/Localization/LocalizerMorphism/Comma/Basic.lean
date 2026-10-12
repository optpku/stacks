/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Computation

/-!
# Comma functors induced by a localizer morphism

A morphism of localizers acts both on ordinary denominator categories and on the localization
comma categories used for pointwise Kan-extension formulas.  This file owns those four functors
and their elementary object and morphism computations; comparison isomorphisms and finality are
kept in separate leaves.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace targetDenominators

/-- The image of a target denominator under a localizer morphism. -/
def obj (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Under W₁ ⊤ X) :
    MorphismProperty.Under W₂ ⊤ (Φ.functor.obj X) :=
  MorphismProperty.Under.mk ⊤ (Φ.functor.map U.hom) (Φ.map _ U.prop)

/-- Compatibility of the mapped target-denominator arrow with its source and target objects. -/
theorem map_comm (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Under W₁ ⊤ X} (f : U ⟶ V) :
    Φ.functor.map U.hom ≫ Φ.functor.map f.right =
      Φ.functor.map V.hom := sorry

/-- The image of a target-denominator refinement under a localizer morphism. -/
def map (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Under W₁ ⊤ X} (f : U ⟶ V) :
    obj Φ U ⟶ obj Φ V :=
  MorphismProperty.Under.homMk (Φ.functor.map f.right) (map_comm Φ f)

/-- Mapping the identity target-denominator refinement gives the identity. -/
theorem map_id (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Under W₁ ⊤ X) :
    map Φ (𝟙 U) = 𝟙 (obj Φ U) := sorry

/-- Mapping a composite of target-denominator refinements preserves composition. -/
theorem map_comp (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V Z : MorphismProperty.Under W₁ ⊤ X}
    (f : U ⟶ V) (g : V ⟶ Z) :
    map Φ (f ≫ g) = map Φ f ≫ map Φ g := sorry

end targetDenominators

/-- The functor on target-denominator categories induced by a localizer morphism. -/
@[stacks 05T5 "localizer morphism on target denominators"]
def targetDenominators (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    MorphismProperty.Under W₁ ⊤ X ⥤
      MorphismProperty.Under W₂ ⊤ (Φ.functor.obj X) where
  obj := targetDenominators.obj Φ
  map := targetDenominators.map Φ
  map_id := targetDenominators.map_id Φ
  map_comp := targetDenominators.map_comp Φ

namespace targetDenominators

/-- The target object of a mapped target denominator is the functorial image of its target. -/
@[simp]
theorem obj_right (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((Φ.targetDenominators X).obj U).right = Φ.functor.obj U.right := sorry

/-- The structural map of a mapped target denominator is the mapped structural map. -/
@[simp]
theorem obj_hom (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((Φ.targetDenominators X).obj U).hom = Φ.functor.map U.hom := sorry

/-- A mapped target-denominator refinement has the expected target component. -/
@[simp]
theorem map_right (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Under W₁ ⊤ X} (f : U ⟶ V) :
    ((Φ.targetDenominators X).map f).right = Φ.functor.map f.right := sorry

end targetDenominators

namespace sourceDenominators

/-- The image of a source denominator under a localizer morphism. -/
def obj (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Over W₁ ⊤ X) :
    MorphismProperty.Over W₂ ⊤ (Φ.functor.obj X) :=
  MorphismProperty.Over.mk ⊤ (Φ.functor.map U.hom) (Φ.map _ U.prop)

/-- Compatibility of the mapped source-denominator arrow with its source and target objects. -/
theorem map_comm (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Over W₁ ⊤ X} (f : U ⟶ V) :
    Φ.functor.map f.left ≫ Φ.functor.map V.hom =
      Φ.functor.map U.hom := sorry

/-- The image of a source-denominator refinement under a localizer morphism. -/
def map (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Over W₁ ⊤ X} (f : U ⟶ V) :
    obj Φ U ⟶ obj Φ V :=
  MorphismProperty.Over.homMk (Φ.functor.map f.left) (map_comm Φ f)

/-- Mapping the identity source-denominator refinement gives the identity. -/
theorem map_id (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Over W₁ ⊤ X) :
    map Φ (𝟙 U) = 𝟙 (obj Φ U) := sorry

/-- Mapping a composite of source-denominator refinements preserves composition. -/
theorem map_comp (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V Z : MorphismProperty.Over W₁ ⊤ X}
    (f : U ⟶ V) (g : V ⟶ Z) :
    map Φ (f ≫ g) = map Φ f ≫ map Φ g := sorry

end sourceDenominators

/-- The functor on source-denominator categories induced by a localizer morphism. -/
@[stacks 05T5 "localizer morphism on source denominators"]
def sourceDenominators (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    MorphismProperty.Over W₁ ⊤ X ⥤
      MorphismProperty.Over W₂ ⊤ (Φ.functor.obj X) where
  obj := sourceDenominators.obj Φ
  map := sourceDenominators.map Φ
  map_id := sourceDenominators.map_id Φ
  map_comp := sourceDenominators.map_comp Φ

namespace sourceDenominators

/-- The source object of a mapped source denominator is the functorial image of its source. -/
@[simp]
theorem obj_left (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((Φ.sourceDenominators X).obj U).left = Φ.functor.obj U.left := sorry

/-- The structural map of a mapped source denominator is the mapped structural map. -/
@[simp]
theorem obj_hom (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((Φ.sourceDenominators X).obj U).hom = Φ.functor.map U.hom := sorry

/-- A mapped source-denominator refinement has the expected source component. -/
@[simp]
theorem map_left (Φ : LocalizerMorphism W₁ W₂) {X : C₁}
    {U V : MorphismProperty.Over W₁ ⊤ X} (f : U ⟶ V) :
    ((Φ.sourceDenominators X).map f).left = Φ.functor.map f.left := sorry

end sourceDenominators

/-- The functor on localization costructured-arrow categories induced by a localizer morphism. -/
@[stacks 05T5 "localizer morphism on localization costructured arrows"]
noncomputable def costructuredArrow (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    CostructuredArrow W₁.Q (W₁.Q.obj X) ⥤
      CostructuredArrow W₂.Q (W₂.Q.obj (Φ.functor.obj X)) :=
  CostructuredArrow.map₂ (Φ.facIso W₁.Q W₂.Q).hom
    ((Φ.facIso W₁.Q W₂.Q).inv.app X)

/-- The functor on localization structured-arrow categories induced by a localizer morphism. -/
@[stacks 05T5 "localizer morphism on localization structured arrows"]
noncomputable def structuredArrow (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    StructuredArrow (W₁.Q.obj X) W₁.Q ⥤
      StructuredArrow (W₂.Q.obj (Φ.functor.obj X)) W₂.Q :=
  StructuredArrow.map₂ ((Φ.facIso W₁.Q W₂.Q).hom.app X)
    (Φ.facIso W₁.Q W₂.Q).inv



end CategoryTheory.LocalizerMorphism
