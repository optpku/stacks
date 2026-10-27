/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pushforward
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Automorphism functors of cofibered-in-groupoids objects

A supplied cleavage of the opposite projection defines a covariant automorphism
functor on the under-category of the image of a total-category object.
-/

@[expose] public section

open CategoryTheory Opposite Under

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

namespace CategoryTheory.Functor.Cleavage

open Fiber

variable {p : F ⥤ C}

/-- The automorphism functor of an object of a category cofibered in groupoids. -/
noncomputable def autFunctor [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F) :
    Under (p.obj x) ⥤ Type v₂ where
  obj f := Aut (pushforwardObj χ f.hom (ofObj p x))
  map φ := TypeCat.ofHom (pushforwardAut χ φ (ofObj p x))
  map_id f := pushforwardAut_id χ f (ofObj p x)
  map_comp φ ψ := pushforwardAut_comp χ φ ψ (ofObj p x)

/-- On objects, the automorphism functor evaluates to automorphisms of the supplied
pushforward in the fibre over the codomain. -/
theorem autFunctor_obj [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F)
    (f : Under (p.obj x)) :
    (autFunctor χ x).obj f = Aut (pushforwardObj χ f.hom (ofObj p x)) := rfl

/-- On morphisms, the automorphism functor acts by the supplied-comparison homomorphism. -/
theorem autFunctor_map [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    (autFunctor χ x).map φ = TypeCat.ofHom (pushforwardAut χ φ (ofObj p x)) := rfl

/-- The comparison of an under-morphism conjugates fibre automorphisms to their images. -/
theorem autFunctor_map_fac [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α : Aut (pushforwardObj χ f.hom (ofObj p x))) :
    pushforwardComparison χ φ (ofObj p x) ≫ ((autFunctor χ x).map φ α).hom.1 =
      α.hom.1 ≫ pushforwardComparison χ φ (ofObj p x) := by
  let y := χ.reindexObj f.hom.op (toOp (ofObj p x))
  let e := fiberInclusion.mapIso (pushforwardCompIso χ φ (ofObj p x))
  let a := Aut.autMulEquivOfIso (toOpFromOpIso y) (toOpAut α)
  have ha : a.hom.1 = α.hom.1.op := by
    change 𝟙 _ ≫ α.hom.1.op ≫ 𝟙 _ = _
    simp
  have hmap : ((χ.reindex φ.right.op).map a.hom).1 ≫ χ.cartesianHom φ.right.op y =
      χ.cartesianHom φ.right.op y ≫ a.hom.1 := by
    letI : p.op.IsStronglyCartesian φ.right.op (χ.cartesianHom φ.right.op y) :=
      (χ.reindexLift φ.right.op y).isStronglyCartesian
    letI : p.op.IsHomLift φ.right.op (χ.cartesianHom φ.right.op y ≫ a.hom.1) :=
      @IsHomLift.comp_lift_id_right' _ _ _ _ p.op _ _
        (χ.reindexObj φ.right.op y).1 y.1 y.1 φ.right.op
        (χ.cartesianHom φ.right.op y)
        (χ.reindexLift φ.right.op y).isStronglyCartesian.toIsHomLift _ a.hom.1 a.hom.2
    exact IsStronglyCartesian.fac p.op φ.right.op (χ.cartesianHom φ.right.op y)
      (Category.id_comp φ.right.op).symm (χ.cartesianHom φ.right.op y ≫ a.hom.1)
  apply Quiver.Hom.op_inj
  change (e.hom ≫ ((χ.reindex φ.right.op).map a.hom).1 ≫ e.inv) ≫
      (e.hom ≫ χ.cartesianHom φ.right.op y) =
    (e.hom ≫ χ.cartesianHom φ.right.op y) ≫ α.hom.1.op
  simp only [Category.assoc]
  erw [e.inv_hom_id_assoc, hmap, ha]
  rfl

/-- The image of an under-morphism under the automorphism functor is a group homomorphism. -/
theorem autFunctor.map_mul [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α β : Aut (pushforwardObj χ f.hom (ofObj p x))) :
    (autFunctor χ x).map φ (α * β) =
      Mul.mul (α := Aut (pushforwardObj χ g.hom (ofObj p x)))
        ((autFunctor χ x).map φ α) ((autFunctor χ x).map φ β) := by
  have hto : toOpAut (α * β) = toOpAut β * toOpAut α := by
    apply Aut.ext
    apply Fiber.hom_ext
    rfl
  have hfrom (γ δ : Aut (χ.reindexObj g.hom.op (toOp (ofObj p x)))) :
      fromOpAut (γ * δ) = fromOpAut δ * fromOpAut γ := by
    apply Aut.ext
    apply Fiber.hom_ext
    rfl
  change pushforwardAut χ φ (ofObj p x) (α * β) =
    pushforwardAut χ φ (ofObj p x) α * pushforwardAut χ φ (ofObj p x) β
  dsimp only [pushforwardAut, pushforwardObj] at *
  erw [hto, _root_.map_mul, _root_.map_mul, _root_.map_mul, hfrom]
  rfl

/-- The automorphism functor sends every under-morphism to a unital map on fibre automorphisms. -/
theorem autFunctor.map_one [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage) (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    (autFunctor χ x).map φ (1 : Aut (pushforwardObj χ f.hom (ofObj p x))) =
      (1 : Aut (pushforwardObj χ g.hom (ofObj p x))) := by
  have hto : toOpAut (1 : Aut (pushforwardObj χ f.hom (ofObj p x))) = 1 := by
    apply Aut.ext
    apply Fiber.hom_ext
    rfl
  have hfrom : fromOpAut (1 : Aut (χ.reindexObj g.hom.op (toOp (ofObj p x)))) = 1 := by
    apply Aut.ext
    apply Fiber.hom_ext
    rfl
  change pushforwardAut χ φ (ofObj p x) 1 = 1
  dsimp only [pushforwardAut, pushforwardObj] at *
  erw [hto, _root_.map_one, _root_.map_one, _root_.map_one, hfrom]
  rfl

end CategoryTheory.Functor.Cleavage

namespace CategoryTheory.Functor

open Fiber Chosen

/-- The automorphism functor of an object of a category cofibered in groupoids. -/
noncomputable def autFunctor (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F) :
    Under (p.obj x) ⥤ Type v₂ :=
  Cleavage.autFunctor (Cleavage.ofIsFibered p.op) x

/-- On objects, the automorphism functor evaluates to automorphisms of the selected
pushforward in the fibre over the codomain. -/
theorem autFunctor_obj (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    (f : Under (p.obj x)) :
    (autFunctor p x).obj f = Aut (pushforwardObj p f.hom (ofObj p x)) := rfl

/-- On morphisms, the automorphism functor acts by the selected-comparison homomorphism. -/
theorem autFunctor_map (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    (autFunctor p x).map φ = TypeCat.ofHom (pushforwardAut p φ (ofObj p x)) := rfl

/-- The comparison of an under-morphism conjugates fibre automorphisms to their images. -/
theorem autFunctor_map_fac (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α : Aut (pushforwardObj p f.hom (ofObj p x))) :
    pushforwardComparison p φ (ofObj p x) ≫ ((autFunctor p x).map φ α).hom.1 =
      α.hom.1 ≫ pushforwardComparison p φ (ofObj p x) :=
  Cleavage.autFunctor_map_fac (Cleavage.ofIsFibered p.op) x φ α

/-- The image of an under-morphism under the automorphism functor is a group homomorphism. -/
theorem autFunctor.map_mul (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α β : Aut (pushforwardObj p f.hom (ofObj p x))) :
    (autFunctor p x).map φ (α * β) =
      Mul.mul (α := Aut (pushforwardObj p g.hom (ofObj p x)))
        ((autFunctor p x).map φ α) ((autFunctor p x).map φ β) :=
  Cleavage.autFunctor.map_mul (Cleavage.ofIsFibered p.op) x φ α β

/-- The automorphism functor sends every under-morphism to a unital map on fibre automorphisms. -/
theorem autFunctor.map_one (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    (autFunctor p x).map φ (1 : Aut (pushforwardObj p f.hom (ofObj p x))) =
      (1 : Aut (pushforwardObj p g.hom (ofObj p x))) :=
  Cleavage.autFunctor.map_one (Cleavage.ofIsFibered p.op) x φ

end CategoryTheory.Functor
