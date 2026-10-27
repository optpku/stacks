/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Restriction
import all ReasLib.AlgebraicGeometry.FiniteHilbertStack.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The category of finite Hilbert lifts

Objects are quintuples `(U, Z, y, x, α)` with `Z ⟶ U` finite locally free
of the specified rank and `α : y|_Z ≅ F(x)`. Morphisms preserve these data
and give pullback squares on the finite locally free schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S}

/-- An object of the degree `d` finite Hilbert category of a 1-morphism `F : X ⟶ Y`. -/
structure Object (F : X ⟶ Y) (d : ℕ) where
  /-- The test scheme over `S`. -/
  U : Over S
  /-- The finite locally free scheme over `U`. -/
  Z : Over S
  /-- The structure morphism `Z ⟶ U`. -/
  π : Z ⟶ U
  /-- `π` is finite locally free of rank `d`. -/
  finiteLocallyFree : IsFiniteLocallyFreeOfRank π.left d
  /-- The fibre object of `Y` over `U`. -/
  y : Y.p.Fiber U
  /-- The fibre object of `X` over `Z`. -/
  x : X.p.Fiber Z
  /-- The isomorphism `y|_Z ≅ F(x)`. -/
  iso : restrictObj y π ≅ (fiberFunctor F Z).obj x

/-- The two paths `α` then `F(a)` and `b|_Z` then `α'` then the cartesian lift of
`F(x')`, compared after postcomposition to `F(x')`. -/
def HomCompatible {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Object F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g) : Prop :=
  ξ.iso.hom.1 ≫ ((fiberFunctor F ξ.Z).map a.hom).1 ≫
      (toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g) =
    (restrictHom b.hom ξ.π).1 ≫ (restrictObj_comp ξ'.y f ξ.π).hom.1 ≫
      (restrictObj_eq ξ'.y hfg).hom.1 ≫ (restrictObj_comp ξ'.y ξ'.π g).inv.1 ≫
        (restrictHom ξ'.iso.hom g).1 ≫
          IsPreFibered.pullbackMap ((fiberFunctor F ξ'.Z).obj ξ'.x).property g

/-- A morphism of quintuples is given by `(f, g, b, a)` with a pullback square on
the finite locally free morphisms. -/
structure Hom {F : X ⟶ Y} {d : ℕ} (ξ ξ' : Object F d) where
  /-- The underlying morphism of test schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism of finite locally free schemes. -/
  g : ξ.Z ⟶ ξ'.Z
  /-- The square of structure morphisms commutes in `(Sch/S)`. -/
  over_comm : ξ.π ≫ f = g ≫ ξ'.π
  /-- `g` realises `Z` as the base change `Z' ×_{U'} U`. -/
  isPullback : IsPullback g.left ξ.π.left ξ'.π.left f.left
  /-- The fibre isomorphism `y ≅ f^* y'`. -/
  b : ξ.y ≅ restrictObj ξ'.y f
  /-- The fibre isomorphism `x ≅ g^* x'`. -/
  a : ξ.x ≅ restrictObj ξ'.x g
  /-- The square of `α`, `b|_Z`, `F(a)`, and `α'` commutes. -/
  comm : HomCompatible f g over_comm b a

section

open CategoryTheory.Functor.Fiber

set_option backward.isDefEq.respectTransparency false

-- These equations compare restriction maps after composition with their cartesian lifts.
section
variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
variable {p : 𝒳 ⥤ Over S} [p.IsFibered]

@[reassoc] private theorem restrictHom_fac {U Z : Over S} {ξ ξ' : p.Fiber U}
    (φ : ξ ⟶ ξ') (f : Z ⟶ U) :
    (fiberInclusion.map (restrictHom φ f)) ≫ IsPreFibered.pullbackMap ξ'.property f =
      IsPreFibered.pullbackMap ξ.property f ≫ fiberInclusion.map φ := by
  haveI := φ.property
  exact IsCartesian.fac p f (IsPreFibered.pullbackMap ξ'.property f)
    (IsPreFibered.pullbackMap ξ.property f ≫ fiberInclusion.map φ)

private theorem restrictObj_comp_hom_fac {U V W : Over S} (ξ : p.Fiber U)
    (f : V ⟶ U) (g : W ⟶ V) :
    (fiberInclusion.map (restrictObj_comp ξ f g).hom) ≫ IsPreFibered.pullbackMap ξ.property (g ≫ f) =
      IsPreFibered.pullbackMap (restrictObj ξ f).property g ≫
        IsPreFibered.pullbackMap ξ.property f := by
  exact IsCartesian.fac p (g ≫ f) _ _

private theorem restrictObj_id_inv_fac {U : Over S} (ξ : p.Fiber U) :
    (fiberInclusion.map (restrictObj_id ξ).inv) ≫ IsPreFibered.pullbackMap ξ.property (𝟙 U) =
      𝟙 (fiberInclusion.obj ξ) := by
  haveI : p.IsHomLift (𝟙 U) (𝟙 (fiberInclusion.obj ξ)) := IsHomLift.id ξ.property
  exact IsCartesian.fac p (𝟙 U) (IsPreFibered.pullbackMap ξ.property (𝟙 U))
    (𝟙 (fiberInclusion.obj ξ))

@[reassoc] private theorem restrictObj_comp_inv_fac {U V W : Over S} (ξ : p.Fiber U)
    (f : V ⟶ U) (g : W ⟶ V) :
    (fiberInclusion.map (restrictObj_comp ξ f g).inv) ≫
        IsPreFibered.pullbackMap (restrictObj ξ f).property g ≫
        IsPreFibered.pullbackMap ξ.property f =
      IsPreFibered.pullbackMap ξ.property (g ≫ f) := by
  exact IsCartesian.fac p (g ≫ f) _ _

@[reassoc] private theorem restrictObj_eq_hom_fac {U Z : Over S} (ξ : p.Fiber U)
    {f g : Z ⟶ U} (h : f = g) :
    (fiberInclusion.map (restrictObj_eq ξ h).hom) ≫ IsPreFibered.pullbackMap ξ.property g =
      IsPreFibered.pullbackMap ξ.property f := by
  subst g
  exact Category.id_comp _

omit [p.IsFibered] in
@[reassoc] private theorem fiberIso_hom_inv_id {U : Over S} {ξ ξ' : p.Fiber U}
    (e : ξ ≅ ξ') :
    fiberInclusion.map e.hom ≫ fiberInclusion.map e.inv = 𝟙 (fiberInclusion.obj ξ) :=
  congrArg Subtype.val e.hom_inv_id

omit [p.IsFibered] in
@[reassoc] private theorem fiberIso_inv_hom_id {U : Over S} {ξ ξ' : p.Fiber U}
    (e : ξ ≅ ξ') :
    fiberInclusion.map e.inv ≫ fiberInclusion.map e.hom = 𝟙 (fiberInclusion.obj ξ') :=
  congrArg Subtype.val e.inv_hom_id

private theorem restrictIso_comp_fac {U V W : Over S}
    {ξ : p.Fiber U} {ξ' : p.Fiber V} {ξ'' : p.Fiber W}
    {f : U ⟶ V} {g : V ⟶ W} (e : ξ ≅ restrictObj ξ' f)
    (e' : ξ' ≅ restrictObj ξ'' g) :
    (fiberInclusion.map (e ≪≫ restrictIso e' f ≪≫ restrictObj_comp ξ'' g f).hom) ≫
        IsPreFibered.pullbackMap ξ''.property (f ≫ g) =
      (fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap ξ'.property f) ≫
        (fiberInclusion.map e'.hom ≫ IsPreFibered.pullbackMap ξ''.property g) := by
  change (fiberInclusion.map e.hom ≫ fiberInclusion.map (restrictHom e'.hom f) ≫
      fiberInclusion.map (restrictObj_comp ξ'' g f).hom) ≫
      IsPreFibered.pullbackMap ξ''.property (f ≫ g) = _
  simp only [Category.assoc, restrictObj_comp_hom_fac]
  simp only [restrictHom_fac_assoc]

end

variable {F : X ⟶ Y} {d : ℕ}

private theorem homCompatible_path_fac {ξ ξ' : Object F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (b : ξ.y ≅ restrictObj ξ'.y f) :
    ((fiberInclusion.map (restrictHom b.hom ξ.π)) ≫ (fiberInclusion.map (restrictObj_comp ξ'.y f ξ.π).hom) ≫
      (fiberInclusion.map (restrictObj_eq ξ'.y hfg).hom) ≫ (fiberInclusion.map (restrictObj_comp ξ'.y ξ'.π g).inv) ≫
        (fiberInclusion.map (restrictHom ξ'.iso.hom g)) ≫
          IsPreFibered.pullbackMap ((fiberFunctor F ξ'.Z).obj ξ'.x).property g) ≫
        fiberInclusion.map ξ'.iso.inv ≫ IsPreFibered.pullbackMap ξ'.y.property ξ'.π =
      IsPreFibered.pullbackMap ξ.y.property ξ.π ≫
        fiberInclusion.map b.hom ≫ IsPreFibered.pullbackMap ξ'.y.property f := by
  simp only [Category.assoc, restrictHom_fac_assoc, fiberIso_hom_inv_id_assoc,
    restrictObj_comp_inv_fac, restrictObj_comp_hom_fac, restrictObj_eq_hom_fac]

-- Postcompose with the inverse comparison and the cartesian lift of π'.
-- Its universal property detects equality of arrows lying over g.
private theorem homCompatible_iff_total {ξ ξ' : Object F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g) :
    HomCompatible f g hfg b a ↔
      fiberInclusion.map ξ.iso.hom ≫
          (toFunctor F).map (fiberInclusion.map a.hom ≫ IsPreFibered.pullbackMap ξ'.x.property g) ≫
          fiberInclusion.map ξ'.iso.inv ≫ IsPreFibered.pullbackMap ξ'.y.property ξ'.π =
        IsPreFibered.pullbackMap ξ.y.property ξ.π ≫
          fiberInclusion.map b.hom ≫ IsPreFibered.pullbackMap ξ'.y.property f := by
  change fiberInclusion.map ξ.iso.hom ≫
      (toFunctor F).map (fiberInclusion.map a.hom) ≫
      (toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g) =
    (fiberInclusion.map (restrictHom b.hom ξ.π)) ≫
      (fiberInclusion.map (restrictObj_comp ξ'.y f ξ.π).hom) ≫
      (fiberInclusion.map (restrictObj_eq ξ'.y hfg).hom) ≫
      (fiberInclusion.map (restrictObj_comp ξ'.y ξ'.π g).inv) ≫
      (fiberInclusion.map (restrictHom ξ'.iso.hom g)) ≫
      IsPreFibered.pullbackMap ((fiberFunctor F ξ'.Z).obj ξ'.x).property g ↔ _
  constructor
  · intro h
    calc
      _ = (fiberInclusion.map ξ.iso.hom ≫
          (toFunctor F).map (fiberInclusion.map a.hom) ≫
          (toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g)) ≫
          fiberInclusion.map ξ'.iso.inv ≫
          IsPreFibered.pullbackMap ξ'.y.property ξ'.π := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := congrArg (fun k => k ≫ fiberInclusion.map ξ'.iso.inv ≫
        IsPreFibered.pullbackMap ξ'.y.property ξ'.π) h
      _ = _ := homCompatible_path_fac f g hfg b
  · intro h
    haveI := ξ.iso.hom.property
    haveI := ((fiberFunctor F ξ.Z).map a.hom).property
    haveI := ξ'.iso.inv.property
    haveI := (restrictHom b.hom ξ.π).property
    haveI := (restrictObj_comp ξ'.y f ξ.π).hom.property
    haveI := (restrictObj_eq ξ'.y hfg).hom.property
    haveI := (restrictObj_comp ξ'.y ξ'.π g).inv.property
    haveI := (restrictHom ξ'.iso.hom g).property
    haveI : Y.p.IsHomLift g
        ((toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g)) :=
      BasedFunctor.preserves_isHomLift (toBasedFunctor F) g _
    have hh := IsStronglyCartesian.ext Y.p ξ'.π
      (IsPreFibered.pullbackMap ξ'.y.property ξ'.π) g
      (ψ := (fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map (fiberInclusion.map a.hom) ≫
        (toFunctor F).map (IsPreFibered.pullbackMap ξ'.x.property g)) ≫ fiberInclusion.map ξ'.iso.inv)
      (ψ' := ((fiberInclusion.map (restrictHom b.hom ξ.π)) ≫ (fiberInclusion.map (restrictObj_comp ξ'.y f ξ.π).hom) ≫
        (fiberInclusion.map (restrictObj_eq ξ'.y hfg).hom) ≫ (fiberInclusion.map (restrictObj_comp ξ'.y ξ'.π g).inv) ≫
          (fiberInclusion.map (restrictHom ξ'.iso.hom g)) ≫
            IsPreFibered.pullbackMap ((fiberFunctor F ξ'.Z).obj ξ'.x).property g) ≫
        fiberInclusion.map ξ'.iso.inv)
      (by
        calc
          _ = _ := by simpa only [Category.assoc, Functor.map_comp] using h
          _ = _ := by
            simpa only [Category.assoc] using (homCompatible_path_fac f g hfg b).symm)
    exact (cancel_mono (fiberInclusion.map ξ'.iso.inv)).mp hh

private theorem hom_ext_total {ξ ξ' : Object F d} {α β : Hom ξ ξ'}
    (hf : α.f = β.f) (hg : α.g = β.g)
    (hb : fiberInclusion.map α.b.hom ≫ IsPreFibered.pullbackMap ξ'.y.property α.f =
      fiberInclusion.map β.b.hom ≫ IsPreFibered.pullbackMap ξ'.y.property β.f)
    (ha : fiberInclusion.map α.a.hom ≫ IsPreFibered.pullbackMap ξ'.x.property α.g =
      fiberInclusion.map β.a.hom ≫ IsPreFibered.pullbackMap ξ'.x.property β.g) : α = β := by
  cases α with
  | mk f g hfg hpb b a hc =>
    cases β with
    | mk f' g' hfg' hpb' b' a' hc' =>
      dsimp only at hf hg hb ha
      subst f'
      subst g'
      have hb' : b = b' := by
        apply Iso.ext
        apply Subtype.ext
        haveI := b.hom.property
        haveI := b'.hom.property
        exact IsCartesian.ext Y.p f (IsPreFibered.pullbackMap ξ'.y.property f) _ _ hb
      have ha' : a = a' := by
        apply Iso.ext
        apply Subtype.ext
        haveI := a.hom.property
        haveI := a'.hom.property
        exact IsCartesian.ext X.p g (IsPreFibered.pullbackMap ξ'.x.property g) _ _ ha
      cases hb'
      cases ha'
      rfl

private theorem idHom_compatible (ξ : Object F d)
    (hfg : ξ.π ≫ 𝟙 ξ.U = 𝟙 ξ.Z ≫ ξ.π) :
    HomCompatible (𝟙 ξ.U) (𝟙 ξ.Z) hfg
      (restrictObj_id ξ.y).symm (restrictObj_id ξ.x).symm := by
  apply (homCompatible_iff_total _ _ _ _ _).2
  simp only [Iso.symm_hom, restrictObj_id_inv_fac]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, fiberIso_hom_inv_id_assoc, Category.comp_id]

private theorem compHom_compatible {ξ ξ' ξ'' : Object F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'')
    (hfg : ξ.π ≫ (α.f ≫ β.f) = (α.g ≫ β.g) ≫ ξ''.π) :
    HomCompatible (α.f ≫ β.f) (α.g ≫ β.g) hfg
      (α.b ≪≫ restrictIso β.b α.f ≪≫ restrictObj_comp ξ''.y β.f α.f)
      (α.a ≪≫ restrictIso β.a α.g ≪≫ restrictObj_comp ξ''.x β.g α.g) := by
  apply (homCompatible_iff_total _ _ _ _ _).2
  simp only [restrictIso_comp_fac]
  let A := fiberInclusion.map α.a.hom ≫
    IsPreFibered.pullbackMap ξ'.x.property α.g
  let B := fiberInclusion.map β.a.hom ≫
    IsPreFibered.pullbackMap ξ''.x.property β.g
  let C := fiberInclusion.map α.b.hom ≫
    IsPreFibered.pullbackMap ξ'.y.property α.f
  let D := fiberInclusion.map β.b.hom ≫
    IsPreFibered.pullbackMap ξ''.y.property β.f
  have hα := (homCompatible_iff_total _ _ _ _ _).1 α.comm
  have hβ := (homCompatible_iff_total _ _ _ _ _).1 β.comm
  change fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map A ≫
      fiberInclusion.map ξ'.iso.inv ≫ IsPreFibered.pullbackMap ξ'.y.property ξ'.π =
    IsPreFibered.pullbackMap ξ.y.property ξ.π ≫ C at hα
  change fiberInclusion.map ξ'.iso.hom ≫ (toFunctor F).map B ≫
      fiberInclusion.map ξ''.iso.inv ≫ IsPreFibered.pullbackMap ξ''.y.property ξ''.π =
    IsPreFibered.pullbackMap ξ'.y.property ξ'.π ≫ D at hβ
  change fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map (A ≫ B) ≫
      fiberInclusion.map ξ''.iso.inv ≫ IsPreFibered.pullbackMap ξ''.y.property ξ''.π =
    IsPreFibered.pullbackMap ξ.y.property ξ.π ≫ (C ≫ D)
  calc
    _ = fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map A ≫
        fiberInclusion.map ξ'.iso.inv ≫
        (fiberInclusion.map ξ'.iso.hom ≫ (toFunctor F).map B ≫
          fiberInclusion.map ξ''.iso.inv ≫
          IsPreFibered.pullbackMap ξ''.y.property ξ''.π) := by
      simp only [Functor.map_comp, fiberIso_inv_hom_id_assoc, Category.assoc]
    _ = fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map A ≫
        fiberInclusion.map ξ'.iso.inv ≫
        (IsPreFibered.pullbackMap ξ'.y.property ξ'.π ≫ D) := by rw [hβ]
    _ = (fiberInclusion.map ξ.iso.hom ≫ (toFunctor F).map A ≫
        fiberInclusion.map ξ'.iso.inv ≫
        IsPreFibered.pullbackMap ξ'.y.property ξ'.π) ≫ D := by
      simp only [Category.assoc]
    _ = (IsPreFibered.pullbackMap ξ.y.property ξ.π ≫ C) ≫ D := by rw [hα]
    _ = _ := Category.assoc _ _ _

end

/-- The identity morphism of a quintuple, using identity restrictions. -/
def idHom {F : X ⟶ Y} {d : ℕ} (ξ : Object F d) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := 𝟙 ξ.Z
  over_comm := by simp
  isPullback := IsPullback.id_horiz ξ.π.left
  b := (restrictObj_id ξ.y).symm
  a := (restrictObj_id ξ.x).symm
  comm := by exact idHom_compatible ξ _

/-- Composite of two morphisms of quintuples. -/
def compHom {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Object F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := α.g ≫ β.g
  over_comm := by
    calc
      ξ.π ≫ (α.f ≫ β.f) = (ξ.π ≫ α.f) ≫ β.f := (Category.assoc _ _ _).symm
      _ = (α.g ≫ ξ'.π) ≫ β.f := by rw [α.over_comm]
      _ = α.g ≫ (β.g ≫ ξ''.π) := by rw [Category.assoc, β.over_comm]
      _ = (α.g ≫ β.g) ≫ ξ''.π := (Category.assoc _ _ _).symm
  isPullback := α.isPullback.paste_horiz β.isPullback
  b := α.b ≪≫ restrictIso β.b α.f ≪≫ restrictObj_comp ξ''.y β.f α.f
  a := α.a ≪≫ restrictIso β.a α.g ≪≫ restrictObj_comp ξ''.x β.g α.g
  comm := by exact compHom_compatible α β _

section

open CategoryTheory.Functor.Fiber

set_option backward.isDefEq.respectTransparency false

-- These equations compare restriction maps after composition with their cartesian lifts.
variable {F : X ⟶ Y} {d : ℕ}

private theorem compHom_b {ξ ξ' ξ'' : Object F d} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (fiberInclusion.map (compHom α β).b.hom) ≫ IsPreFibered.pullbackMap ξ''.y.property (compHom α β).f =
      ((fiberInclusion.map α.b.hom) ≫ IsPreFibered.pullbackMap ξ'.y.property α.f) ≫
        ((fiberInclusion.map β.b.hom) ≫ IsPreFibered.pullbackMap ξ''.y.property β.f) :=
  restrictIso_comp_fac α.b β.b

private theorem compHom_a {ξ ξ' ξ'' : Object F d} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (fiberInclusion.map (compHom α β).a.hom) ≫ IsPreFibered.pullbackMap ξ''.x.property (compHom α β).g =
      ((fiberInclusion.map α.a.hom) ≫ IsPreFibered.pullbackMap ξ'.x.property α.g) ≫
        ((fiberInclusion.map β.a.hom) ≫ IsPreFibered.pullbackMap ξ''.x.property β.g) :=
  restrictIso_comp_fac α.a β.a

private theorem idHom_b (ξ : Object F d) :
    (fiberInclusion.map (idHom ξ).b.hom) ≫ IsPreFibered.pullbackMap ξ.y.property (𝟙 ξ.U) =
      𝟙 (fiberInclusion.obj ξ.y) :=
  restrictObj_id_inv_fac ξ.y

private theorem idHom_a (ξ : Object F d) :
    (fiberInclusion.map (idHom ξ).a.hom) ≫ IsPreFibered.pullbackMap ξ.x.property (𝟙 ξ.Z) =
      𝟙 (fiberInclusion.obj ξ.x) :=
  restrictObj_id_inv_fac ξ.x

end

set_option backward.isDefEq.respectTransparency false in
/-- Quintuples with finite locally free structure maps of rank `d`, together with
pullback-compatible morphisms, form a bundled category. -/
def category (F : X ⟶ Y) (d : ℕ) : Cat.{u, u + 1} :=
  ⟨Object F d, {
    Hom := Hom
    id := idHom
    comp := fun α β ↦ compHom α β
    id_comp := by
      intro ξ ξ' α
      apply hom_ext_total (α := compHom (idHom ξ) α) (β := α)
        (Category.id_comp α.f) (Category.id_comp α.g)
      · change (Fiber.fiberInclusion.map (compHom (idHom ξ) α).b.hom) ≫
            IsPreFibered.pullbackMap ξ'.y.property ((idHom ξ).f ≫ α.f) = _
        erw [compHom_b, idHom_b, Category.id_comp]
      · change (Fiber.fiberInclusion.map (compHom (idHom ξ) α).a.hom) ≫
            IsPreFibered.pullbackMap ξ'.x.property ((idHom ξ).g ≫ α.g) = _
        erw [compHom_a, idHom_a, Category.id_comp]
    comp_id := by
      intro ξ ξ' α
      apply hom_ext_total (α := compHom α (idHom ξ')) (β := α)
        (Category.comp_id α.f) (Category.comp_id α.g)
      · change (Fiber.fiberInclusion.map (compHom α (idHom ξ')).b.hom) ≫
            IsPreFibered.pullbackMap ξ'.y.property (α.f ≫ (idHom ξ').f) = _
        erw [compHom_b, idHom_b, Category.comp_id]
      · change (Fiber.fiberInclusion.map (compHom α (idHom ξ')).a.hom) ≫
            IsPreFibered.pullbackMap ξ'.x.property (α.g ≫ (idHom ξ').g) = _
        erw [compHom_a, idHom_a, Category.comp_id]
    assoc := by
      intro ξ ξ' ξ'' ξ''' α β γ
      apply hom_ext_total (Category.assoc α.f β.f γ.f) (Category.assoc α.g β.g γ.g)
      · change (Fiber.fiberInclusion.map (compHom (compHom α β) γ).b.hom) ≫
            IsPreFibered.pullbackMap ξ'''.y.property ((compHom α β).f ≫ γ.f) =
          (Fiber.fiberInclusion.map (compHom α (compHom β γ)).b.hom) ≫
            IsPreFibered.pullbackMap ξ'''.y.property (α.f ≫ (compHom β γ).f)
        erw [compHom_b, compHom_b, compHom_b, compHom_b]
        exact Category.assoc _ _ _
      · change (Fiber.fiberInclusion.map (compHom (compHom α β) γ).a.hom) ≫
            IsPreFibered.pullbackMap ξ'''.x.property ((compHom α β).g ≫ γ.g) =
          (Fiber.fiberInclusion.map (compHom α (compHom β γ)).a.hom) ≫
            IsPreFibered.pullbackMap ξ'''.x.property (α.g ≫ (compHom β γ).g)
        erw [compHom_a, compHom_a, compHom_a, compHom_a]
        exact Category.assoc _ _ _ }⟩

/-- The carrier of the category of finite locally free degree-`d` lifts along `F`. -/
abbrev Obj (F : X ⟶ Y) (d : ℕ) : Type (u + 1) := category F d

/-- Package a quintuple `(U, Z, y, x, α)` as an object of `H_d(X/Y)`. -/
def Obj.of {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) : Obj F d where
  U := U
  Z := Z
  π := π
  finiteLocallyFree := hπ
  y := y
  x := x
  iso := iso

/-- The constructor `Obj.of` stores the supplied test scheme. -/
theorem Obj.of_U {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).U = U := rfl

/-- The constructor `Obj.of` stores the supplied finite locally free scheme. -/
theorem Obj.of_Z {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).Z = Z := rfl

/-- The constructor `Obj.of` stores the supplied structure morphism. -/
theorem Obj.of_π {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).π = π := rfl

/-- The constructor `Obj.of` stores the supplied fibre object of `Y`. -/
theorem Obj.of_y {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).y = y := rfl

/-- The constructor `Obj.of` stores the supplied fibre object of `X`. -/
theorem Obj.of_x {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).x = x := rfl

/-- The constructor `Obj.of` stores the supplied isomorphism `y|_Z ≅ F(x)`. -/
theorem Obj.of_iso {F : X ⟶ Y} {d : ℕ} (U Z : Over S) (π : Z ⟶ U)
    (hπ : IsFiniteLocallyFreeOfRank π.left d) (y : Y.p.Fiber U)
    (x : X.p.Fiber Z)
    (iso : restrictObj y π ≅ (fiberFunctor F Z).obj x) :
    (Obj.of U Z π hπ y x iso).iso = iso := rfl

/-- An object of `H_d(X/Y)` has `Z ⟶ U` finite locally free of rank `d`. -/
theorem Obj.spec {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) :
    IsFiniteLocallyFreeOfRank ξ.π.left d := ξ.finiteLocallyFree

/-- Assemble a morphism of `H_d(X/Y)` from `(f, g, b, a)`, the pullback square,
and the commutativity square. -/
def Hom.homMk {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    Hom ξ ξ' where
  f := f
  g := g
  over_comm := hfg
  isPullback := hpb
  b := b
  a := a
  comm := hcomm

/-- The constructor `homMk` stores the supplied map of test schemes. -/
theorem Hom.homMk_f {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).f = f := rfl

/-- The constructor `homMk` stores the supplied map of finite locally free schemes. -/
theorem Hom.homMk_g {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).g = g := rfl

/-- The constructor `homMk` stores the supplied fibre isomorphism `b`. -/
theorem Hom.homMk_b {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).b = b := rfl

/-- The constructor `homMk` stores the supplied fibre isomorphism `a`. -/
theorem Hom.homMk_a {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).a = a := rfl

/-- The constructor `homMk` stores the supplied commutativity proof. -/
theorem Hom.homMk_comm {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d}
    (f : ξ.U ⟶ ξ'.U) (g : ξ.Z ⟶ ξ'.Z) (hfg : ξ.π ≫ f = g ≫ ξ'.π)
    (hpb : IsPullback g.left ξ.π.left ξ'.π.left f.left)
    (b : ξ.y ≅ restrictObj ξ'.y f) (a : ξ.x ≅ restrictObj ξ'.x g)
    (hcomm : HomCompatible f g hfg b a) :
    (Hom.homMk f g hfg hpb b a hcomm).comm = hcomm := rfl

/-- A morphism of `H_d(X/Y)` induces a pullback square of finite locally free
morphisms. -/
theorem Hom.spec {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : Hom ξ ξ') :
    IsPullback φ.g.left ξ.π.left ξ'.π.left φ.f.left := φ.isPullback

/-- The identity morphism of `p` is the identity of the test scheme. -/
theorem idHom_f {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (idHom ξ).f = 𝟙 ξ.U := rfl

/-- Composition in `H_d(X/Y)` projects to composition of test-scheme morphisms. -/
theorem compHom_f {F : X ⟶ Y} {d : ℕ} {ξ ξ' ξ'' : Obj F d}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor sending `(U, Z, y, x, α)` to `U`. -/
def p (F : X ⟶ Y) (d : ℕ) : Obj F d ⥤ Over S where
  obj ξ := ξ.U
  map φ := φ.f
  map_id := idHom_f
  map_comp := compHom_f

/-- The object part of `p` is the underlying test scheme. -/
theorem p_obj {F : X ⟶ Y} {d : ℕ} (ξ : Obj F d) : (p F d).obj ξ = ξ.U := rfl

/-- The morphism part of `p` is the underlying map of test schemes. -/
theorem p_map {F : X ⟶ Y} {d : ℕ} {ξ ξ' : Obj F d} (φ : ξ ⟶ ξ') :
    (p F d).map φ = φ.f := rfl

/-- The forgetful functor `p : H_d(X/Y) ⟶ (Sch/S)` is fibered in groupoids. -/
instance instIsFiberedInGroupoids (F : X ⟶ Y) (d : ℕ) :
    Functor.IsFibered.InGroupoids (p F d) := sorry

end AlgebraicGeometry.FiniteHilbertStack
