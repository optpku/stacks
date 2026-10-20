module

public import Mathlib.CategoryTheory.Category.Basic
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

@[expose] public section

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- A morphism of module sheaves on `Cris(X / S)`. -/
structure CrisModuleSheafHom
    (F G : CrisModuleSheaf S I γ h_compatible X x₀) where
  /-- The component on each small crystalline object. -/
  app : ∀ T : smallCrystallineSite S I γ h_compatible X x₀, F.obj T ⟶ G.obj T
  /-- Naturality with respect to morphisms of small crystalline objects. -/
  natural : ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
      (f : A ⟶ B),
      (Scheme.Modules.pullback f.hom.thickening).map (app B) ≫ G.comparison f =
        F.comparison f ≫ app A

/-- Construct a morphism of `Cris(X / S)`-module sheaves from components. -/
def CrisModuleSheafHom.of
    {F G : CrisModuleSheaf S I γ h_compatible X x₀}
    (app : ∀ T : smallCrystallineSite S I γ h_compatible X x₀, F.obj T ⟶ G.obj T)
    (natural : ∀ {A B : smallCrystallineSite S I γ h_compatible X x₀}
      (f : A ⟶ B),
      (Scheme.Modules.pullback f.hom.thickening).map (app B) ≫ G.comparison f =
        F.comparison f ≫ app A) :
    CrisModuleSheafHom F G :=
  { app, natural }

/-- The identity morphism of a `Cris(X / S)`-module sheaf. -/
def CrisModuleSheafHom.id (F : CrisModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheafHom F F :=
  CrisModuleSheafHom.of (fun T ↦ 𝟙 (F.obj T)) sorry

/-- Composition of morphisms of `Cris(X / S)`-module sheaves. -/
def CrisModuleSheafHom.comp
    {F G H : CrisModuleSheaf S I γ h_compatible X x₀}
    (f : CrisModuleSheafHom F G) (g : CrisModuleSheafHom G H) :
    CrisModuleSheafHom F H :=
  CrisModuleSheafHom.of (fun T ↦ f.app T ≫ g.app T) sorry

/-- The category of module sheaves on `Cris(X / S)`. -/
instance crisModuleSheafCategory :
    Category (CrisModuleSheaf S I γ h_compatible X x₀) where
  Hom := CrisModuleSheafHom
  id := CrisModuleSheafHom.id
  comp := CrisModuleSheafHom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Evaluation of a small crystalline module sheaf at an object of `Cris(X / S)`. -/
def crystallineEval
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (T.obj.1.thickening).Modules :=
  F.obj T

/-- Evaluation at `T` recovers the objectwise module sheaf. -/
theorem crystallineEval_eq
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    crystallineEval F T = F.obj T := sorry

/-- Evaluation at a fixed object `T` of `Cris(X / S)`, as a functor. -/
def crystallineEvalFunctor
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ ⥤ (T.obj.1.thickening).Modules where
  obj F := crystallineEval F T
  map f := f.app T
