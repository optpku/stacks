/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monotonicity of Right Resolutions

A right resolution remains a right resolution after weakening either the property required of
its model or the morphism property required of its comparison.  This file packages that operation
on objects and morphisms and records its functorial compatibility with the model and comparison.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty.RightResolution

variable {D : Type u} [Category.{v} D]
  {P Q : ObjectProperty D} {S T : MorphismProperty D} {X : D}

/-- Weaken the model and comparison properties of a right resolution. -/
@[stacks 0GSL "monotonicity of right resolutions"]
def mapOfLE (hP : P ≤ Q) (hS : S ≤ T) (R : RightResolution P S X) :
    RightResolution Q T X :=
  RightResolution.mk ((P.ιOfLE hP).obj R.model) R.comparison
    (hS _ R.hw)

namespace mapOfLE

/-- Weakening a right resolution maps its bundled model along `ObjectProperty.ιOfLE`. -/
@[simp]
theorem model (hP : P ≤ Q) (hS : S ≤ T) (R : RightResolution P S X) :
    (R.mapOfLE hP hS).model = (P.ιOfLE hP).obj R.model := sorry

/-- Weakening a right resolution retains its ambient model object. -/
@[simp]
theorem object (hP : P ≤ Q) (hS : S ≤ T) (R : RightResolution P S X) :
    (R.mapOfLE hP hS).object = R.object := sorry

/-- Weakening a right resolution retains its comparison morphism. -/
@[simp]
theorem comparison (hP : P ≤ Q) (hS : S ≤ T) (R : RightResolution P S X) :
    (R.mapOfLE hP hS).comparison = R.comparison := sorry

/-- The weakened model map satisfies the right-resolution comparison square. -/
theorem hom_comm (hP : P ≤ Q) (hS : S ≤ T)
    {R R' : RightResolution P S X} (f : R ⟶ R') :
    (R.mapOfLE hP hS).comparison ≫
        Q.ι.map ((P.ιOfLE hP).map (modelHom f)) =
      (R'.mapOfLE hP hS).comparison := sorry

/-- Map a morphism of right resolutions after weakening its two defining properties. -/
def hom (hP : P ≤ Q) (hS : S ≤ T)
    {R R' : RightResolution P S X} (f : R ⟶ R') :
    R.mapOfLE hP hS ⟶ R'.mapOfLE hP hS where
  f := (P.ιOfLE hP).map (modelHom f)
  comm := hom_comm hP hS f

/-- The bundled model map of a weakened right-resolution morphism is induced by
`ObjectProperty.ιOfLE`. -/
@[simp]
theorem hom_modelHom (hP : P ≤ Q) (hS : S ≤ T)
    {R R' : RightResolution P S X} (f : R ⟶ R') :
    modelHom (hom hP hS f) = (P.ιOfLE hP).map (modelHom f) := sorry

/-- Weakening a right-resolution morphism retains its ambient morphism. -/
@[simp]
theorem hom_hom (hP : P ≤ Q) (hS : S ≤ T)
    {R R' : RightResolution P S X} (f : R ⟶ R') :
    RightResolution.hom (hom hP hS f) = RightResolution.hom f := sorry

/-- Weakening preserves identity morphisms of right resolutions. -/
@[simp]
theorem hom_id (hP : P ≤ Q) (hS : S ≤ T) (R : RightResolution P S X) :
    hom hP hS (𝟙 R) = 𝟙 (R.mapOfLE hP hS) := sorry

/-- Weakening preserves composition of right-resolution morphisms. -/
@[simp]
theorem hom_comp (hP : P ≤ Q) (hS : S ≤ T)
    {R R' R'' : RightResolution P S X} (f : R ⟶ R') (g : R' ⟶ R'') :
    hom hP hS (f ≫ g) = hom hP hS f ≫ hom hP hS g := sorry

/-- Functorially weaken the model and comparison properties of right resolutions. -/
@[stacks 0GSL "functorial monotonicity of right resolutions"]
def functor (hP : P ≤ Q) (hS : S ≤ T) (X : D) :
    RightResolution P S X ⥤ RightResolution Q T X where
  obj R := R.mapOfLE hP hS
  map f := hom hP hS f
  map_id := hom_id hP hS
  map_comp := hom_comp hP hS

/-- The monotonicity functor acts on objects by `mapOfLE`. -/
@[simp]
theorem functor_obj (hP : P ≤ Q) (hS : S ≤ T) (X : D)
    (R : RightResolution P S X) :
    (functor hP hS X).obj R = R.mapOfLE hP hS := sorry

/-- The monotonicity functor acts on morphisms by `mapOfLE.hom`. -/
@[simp]
theorem functor_map (hP : P ≤ Q) (hS : S ≤ T) (X : D)
    {R R' : RightResolution P S X} (f : R ⟶ R') :
    (functor hP hS X).map f = hom hP hS f := sorry

/-- The right-resolution monotonicity functor is full. -/
instance functor_full (hP : P ≤ Q) (hS : S ≤ T) (X : D) :
    (functor hP hS X).Full := sorry

/-- The right-resolution monotonicity functor is faithful. -/
instance functor_faithful (hP : P ≤ Q) (hS : S ≤ T) (X : D) :
    (functor hP hS X).Faithful := sorry

/-- The monotonicity functor followed by the weaker model functor is the original model functor
followed by the full-subcategory inclusion induced by `hP`. -/
theorem functor_comp_modelFunctor (hP : P ≤ Q) (hS : S ≤ T) (X : D) :
    functor hP hS X ⋙ modelFunctor Q T X =
      modelFunctor P S X ⋙ P.ιOfLE hP := sorry

/-- The monotonicity functor does not change the ambient model functor. -/
theorem functor_comp_objectFunctor (hP : P ≤ Q) (hS : S ≤ T) (X : D) :
    functor hP hS X ⋙ objectFunctor Q T X = objectFunctor P S X := sorry

/-- The natural comparison of weakened right resolutions has the same components as the original
comparison. -/
@[simp]
theorem comparison_app (hP : P ≤ Q) (hS : S ≤ T)
    (X : D) (R : RightResolution P S X) :
    (comparisonNatTrans Q T X).app ((functor hP hS X).obj R) =
      (comparisonNatTrans P S X).app R := sorry

/-- Weakening by reflexive inequalities does not change a right resolution. -/
@[simp]
theorem refl (R : RightResolution P S X) : R.mapOfLE le_rfl le_rfl = R := sorry

/-- Successive weakenings of a right resolution agree with weakening by the composite
inequalities. -/
theorem trans {R' : ObjectProperty D} {U : MorphismProperty D}
    (hPQ : P ≤ Q) (hQR : Q ≤ R') (hST : S ≤ T) (hTU : T ≤ U)
    (R : RightResolution P S X) :
    (R.mapOfLE hPQ hST).mapOfLE hQR hTU =
      R.mapOfLE (hPQ.trans hQR) (hST.trans hTU) := sorry

/-- Reflexive weakening is the identity functor on right resolutions. -/
theorem functor_id :
    functor (le_refl P) (le_refl S) X = Functor.id (RightResolution P S X) := sorry

/-- Composing right-resolution weakening functors agrees with weakening by composite
inequalities. -/
theorem functor_comp {R : ObjectProperty D} {U : MorphismProperty D}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (hST : S ≤ T) (hTU : T ≤ U) :
    functor hPQ hST X ⋙ functor hQR hTU X =
      functor (hPQ.trans hQR) (hST.trans hTU) X := sorry

end mapOfLE

end CategoryTheory.ObjectProperty.RightResolution

namespace CategoryTheory.ObjectProperty.HasRightResolutions

variable {D : Type u} [Category.{v} D]
  {P Q : ObjectProperty D} {S T : MorphismProperty D}

/-- Weakening model and comparison properties preserves existence of right resolutions. -/
theorem mono (h : HasRightResolutions P S) (hP : P ≤ Q) (hS : S ≤ T) :
    HasRightResolutions Q T := sorry

end CategoryTheory.ObjectProperty.HasRightResolutions


