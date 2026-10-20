/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Coimage
public import ReasLib.AlgebraicGeometry.FormalDeformation.SubringOver
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.CategoryTheory.Cofibered.Pushforward

/-! # Pushforward of subring-over objects and minimality -/

@[expose] public section

open CategoryTheory IsLocalRing
open Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- A chosen strongly cocartesian lift of the coimage projection of `p.map (a.hom ≫ φ)`. -/
noncomputable def pushforwardLift [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : Over y) :
    StronglyCocartesianLift p (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ))) :=
  StronglyCocartesianLift.ofCleavage (cleavageOp p)
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))

/-- The unique factorization `x' ⟶ x` over the coimage inclusion of `p.map (a.hom ≫ φ)`. -/
noncomputable def pushforwardArrow [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : Over y) : (pushforwardLift p φ a).target ⟶ x :=
  IsStronglyCocartesian.map p
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))
    (pushforwardLift p φ a).hom
    (ArtinianLocalAlgCat.image_fac (p.map (a.hom ≫ φ))).symm
    (a.hom ≫ φ)

/-- The comparison of coimages induced by a morphism of over-objects. -/
private theorem pushforwardSquare {x y : F} (φ : y ⟶ x) {a b : Over y} (η : a ⟶ b) :
    p.map (a.hom ≫ φ) ≫ 𝟙 (p.obj x) = p.map η.left ≫ p.map (b.hom ≫ φ) :=
  (Category.comp_id (p.map (a.hom ≫ φ))).trans
    ((p.congr_map
        ((congrArg (fun k => k ≫ φ) (Over.w η).symm).trans
          (Category.assoc η.left b.hom φ))).trans
      (p.map_comp η.left (b.hom ≫ φ)))

/-- The base morphism of a morphism of pushforward lifts, as a map of coimages. -/
noncomputable def pushforwardMapBase [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    ArtinianLocalAlgCat.image (p.map (a.hom ≫ φ)) ⟶
      p.obj (pushforwardLift p φ b).target :=
  ArtinianLocalAlgCat.imageMap (p.map (a.hom ≫ φ)) (p.map (b.hom ≫ φ))
      (p.map η.left) (𝟙 (p.obj x)) (by exact pushforwardSquare p φ η) ≫
    eqToHom (StronglyCocartesianLift.targetObj (pushforwardLift p φ b)).symm

/-- The identity used to apply the strongly cocartesian universal property to a morphism
of over-objects. -/
private theorem pushforwardMap_fac [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    p.map (η.left ≫ (pushforwardLift p φ b).hom) =
      ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)) ≫ pushforwardMapBase p φ η := by
  have hquot :
      p.map η.left ≫ ArtinianLocalAlgCat.toImage (p.map (b.hom ≫ φ)) =
        ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)) ≫
          ArtinianLocalAlgCat.imageMap (p.map (a.hom ≫ φ)) (p.map (b.hom ≫ φ))
            (p.map η.left) (𝟙 (p.obj x)) (pushforwardSquare p φ η) :=
    ArtinianLocalAlgCat.hom_ext
      (Ideal.quotient_map_comp_mkₐ _ (p.map η.left).hom
        (ArtinianLocalAlgCat.imageMap_le _ _ _ _ (pushforwardSquare p φ η))).symm
  rw [p.map_comp η.left (pushforwardLift p φ b).hom, IsHomLift.fac' p
    (ArtinianLocalAlgCat.toImage (p.map (b.hom ≫ φ))) (pushforwardLift p φ b).hom]
  simpa only [pushforwardMapBase, eqToHom_refl, Category.id_comp, Category.assoc] using
    congrArg (fun f => f ≫ eqToHom
      (IsHomLift.codomain_eq p (ArtinianLocalAlgCat.toImage (p.map (b.hom ≫ φ)))
        (pushforwardLift p φ b).hom).symm) hquot

/-- The morphism of pushforward targets induced by a morphism of over-objects. -/
noncomputable def pushforwardMap [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    (pushforwardLift p φ a).target ⟶ (pushforwardLift p φ b).target :=
  IsStronglyCocartesian.map p
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))
    (pushforwardLift p φ a).hom
    (g := pushforwardMapBase p φ η)
    (f' := p.map (η.left ≫ (pushforwardLift p φ b).hom))
    (by exact pushforwardMap_fac p φ η)
    (η.left ≫ (pushforwardLift p φ b).hom)

/-- The cocartesian factorization arrow lies over an injective algebra map. -/
theorem pushforwardArrow_injective [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : Over y) : Function.Injective (p.map (pushforwardArrow p φ a)).hom := sorry

/-- A map between pushforward targets commutes with their arrows to the fixed target. -/
theorem pushforwardMap_over [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    pushforwardMap p φ η ≫ pushforwardArrow p φ b = pushforwardArrow p φ a := sorry

namespace SubringOver

/-- Push a subring-over object along an arrow using its coimage factorization. -/
noncomputable def pushforwardObj [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) : SubringOver p x :=
  mk (pushforwardArrow p φ a.obj) (pushforwardArrow_injective p φ a.obj)

/-- Push a morphism of subring-over objects along an arrow. -/
noncomputable def pushforwardHom [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : SubringOver p y} (η : a ⟶ b) : pushforwardObj p φ a ⟶ pushforwardObj p φ b :=
  InducedCategory.homMk (Over.homMk (pushforwardMap p φ η.hom) (pushforwardMap_over p φ η.hom))

/-- Pushforward of subring-over morphisms preserves identities. -/
theorem pushforward_map_id [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) : pushforwardHom p φ (𝟙 a) = 𝟙 (pushforwardObj p φ a) := sorry

/-- Pushforward of subring-over morphisms preserves composition. -/
theorem pushforward_map_comp [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b c : SubringOver p y} (η : a ⟶ b) (θ : b ⟶ c) :
    pushforwardHom p φ (η ≫ θ) = pushforwardHom p φ η ≫ pushforwardHom p φ θ := sorry

/-- The functor sending a subring-over object to its pushforward along an arrow. -/
noncomputable def pushforward [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x) :
    SubringOver p y ⥤ SubringOver p x where
  obj := pushforwardObj p φ
  map := pushforwardHom p φ
  map_id := pushforward_map_id p φ
  map_comp := pushforward_map_comp p φ

/-- The domain of `pushforward p φ` applied to `a` lies over the coimage of
`p.map (arrow a ≫ φ)`. -/
theorem pushforward_obj_image [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    p.obj ((pushforward p φ).obj a).obj.left =
      ArtinianLocalAlgCat.image (p.map (arrow a ≫ φ)) := sorry

/-- The underlying arrow of `pushforward p φ` applied to `a` is the cocartesian
factorization of `arrow a ≫ φ`. -/
theorem pushforward_obj_arrow [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    arrow ((pushforward p φ).obj a) = pushforwardArrow p φ a.obj := sorry

/-- The pushforward of an object of `S_y` is an object of `S_x`. -/
theorem pushforward_obj_spec [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    Function.Injective (p.map (arrow ((pushforward p φ).obj a))).hom := sorry

/-- For a cofibered functor satisfying Schlessinger's condition (S1), pushforward
preserves minimal subring-over objects. -/
theorem pushforward_preserves_isMinimal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    {a : SubringOver p y} (ha : IsMinimal a) :
    IsMinimal ((pushforward p φ).obj a) := sorry

/-- Over a surjective base map, every minimal subring-over object is isomorphic
to the pushforward of a minimal subring-over object. -/
theorem exists_isMinimal_of_surjective (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    (hφ : Function.Surjective (p.map φ).hom) (a : SubringOver p x) (ha : IsMinimal a) :
    ∃ b : SubringOver p y, IsMinimal b ∧ Nonempty ((pushforward p φ).obj b ≅ a) := sorry

end SubringOver

end CategoryTheory.Functor
