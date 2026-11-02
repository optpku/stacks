/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Basic
import all ReasLib.AlgebraicGeometry.FiniteHilbertStack.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction

/-!
# The 1-morphism of finite Hilbert stacks induced by a morphism of sources

A 1-morphism `G : X' ⟶ X` of categories fibred in groupoids induces
`H_d(X'/Y) ⟶ H_d(X/Y)` by applying the fibre functor of `G` to the `X`-component
of a quintuple and composing the comparison isomorphism with `fiberFunctor.comp`.
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
variable {X' X Y : GroupoidsOver S}

/-- The category fibred in groupoids `H_d(X/Y)` associated to the forgetful
functor `p F d`. -/
abbrev toGroupoids (F : X ⟶ Y) (d : ℕ) : GroupoidsOver S :=
  ofFunctor (p F d)

/-- The projection of `toGroupoids F d` is the forgetful functor `p F d`. -/
theorem toGroupoids_p (F : X ⟶ Y) (d : ℕ) : (toGroupoids F d).p = p F d := rfl

/-- Fibrewise comparison of `G ≫ F` with the composite of the fibre functors of
`G` and `F`. -/
def mapIso (G : X' ⟶ X) (F : X ⟶ Y) {Z : Over S} (x' : X'.p.Fiber Z) :
    (fiberFunctor (G ≫ F) Z).obj x' ≅
      (fiberFunctor F Z).obj ((fiberFunctor G Z).obj x') :=
  eqToIso (congrArg (fun H ↦ H.obj x') (fiberFunctor.comp G F Z))

/-- Object part of the induced 1-morphism: copy `(U, Z, π, y)` and apply the
fibre functor of `G` to `x`. -/
abbrev mapObj (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} (ξ : Obj (G ≫ F) d) : Obj F d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree ξ.y ((fiberFunctor G ξ.Z).obj ξ.x)
    (ξ.iso ≪≫ mapIso G F ξ.x)

section

set_option backward.isDefEq.respectTransparency false

-- Compare fibre isomorphisms after their chosen cartesian lifts in the total category.
private theorem mapRestriction_fac (G : X' ⟶ X) {U Z : Over S}
    (x : X'.p.Fiber U) (f : Z ⟶ U) :
    (fiberFunctor_restrictObj G x f).hom.1 ≫
        IsPreFibered.pullbackMap ((fiberFunctor G U).obj x).property f =
      (toFunctor G).map (IsPreFibered.pullbackMap x.property f) := by
  letI := IsPreFibered.pullbackMap.IsCartesian ((fiberFunctor G U).obj x).property f
  letI := IsPreFibered.pullbackMap.IsCartesian x.property f
  letI := BasedFunctor.preserves_isHomLift (toBasedFunctor G) f
    (IsPreFibered.pullbackMap x.property f)
  exact IsCartesian.fac X.p f _ _

private theorem mapRestrictionIso_fac (G : X' ⟶ X) {U Z : Over S}
    {x : X'.p.Fiber Z} {x' : X'.p.Fiber U} (f : Z ⟶ U)
    (a : x ≅ restrictObj x' f) :
    ((fiberFunctor G Z).mapIso a ≪≫ fiberFunctor_restrictObj G x' f).hom.1 ≫
        IsPreFibered.pullbackMap ((fiberFunctor G U).obj x').property f =
      (toFunctor G).map (a.hom.1 ≫ IsPreFibered.pullbackMap x'.property f) := by
  change ((toFunctor G).map a.hom.1 ≫ (fiberFunctor_restrictObj G x' f).hom.1) ≫ _ = _
  erw [Category.assoc, mapRestriction_fac, CategoryTheory.Functor.map_comp]

/-- Morphism part of the induced 1-morphism: the same `(f, g, b)` with `a`
transported by the fibre functor of `G`. -/
def mapHom (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} {ξ ξ' : Obj (G ≫ F) d}
    (φ : Hom ξ ξ') : Hom (mapObj G F ξ) (mapObj G F ξ') where
  f := φ.f
  g := φ.g
  over_comm := φ.over_comm
  isPullback := φ.isPullback
  b := φ.b
  a := (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g
  comm := by
    apply (homCompatible_iff_total _ _ _ _ _).2
    change (ξ.iso.hom.1 ≫ 𝟙 _) ≫
        (toFunctor F).map
          (((fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g).hom.1 ≫
            IsPreFibered.pullbackMap ((fiberFunctor G ξ'.Z).obj ξ'.x).property φ.g) ≫
        (𝟙 _ ≫ ξ'.iso.inv.1) ≫ IsPreFibered.pullbackMap ξ'.y.property ξ'.π =
      IsPreFibered.pullbackMap ξ.y.property ξ.π ≫ φ.b.hom.1 ≫
        IsPreFibered.pullbackMap ξ'.y.property φ.f
    erw [mapRestrictionIso_fac]
    have h := (homCompatible_iff_total _ _ _ _ _).1 φ.comm
    change ξ.iso.hom.1 ≫
        (toFunctor F).map ((toFunctor G).map
          (φ.a.hom.1 ≫ IsPreFibered.pullbackMap ξ'.x.property φ.g)) ≫
        ξ'.iso.inv.1 ≫ IsPreFibered.pullbackMap ξ'.y.property ξ'.π =
      IsPreFibered.pullbackMap ξ.y.property ξ.π ≫ φ.b.hom.1 ≫
        IsPreFibered.pullbackMap ξ'.y.property φ.f at h
    simpa only [Category.comp_id, Category.id_comp] using h

private theorem mapHom_a_fac (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ}
    {ξ ξ' : Obj (G ≫ F) d} (φ : Hom ξ ξ') :
    Fiber.fiberInclusion.map (mapHom G F φ).a.hom ≫
        IsPreFibered.pullbackMap ((fiberFunctor G ξ'.Z).obj ξ'.x).property φ.g =
      (toFunctor G).map (Fiber.fiberInclusion.map φ.a.hom ≫
        IsPreFibered.pullbackMap ξ'.x.property φ.g) :=
  mapRestrictionIso_fac G φ.g φ.a

/-- The induced map on finite Hilbert morphisms preserves identities. -/
theorem mapHom_id (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} (ξ : Obj (G ≫ F) d) :
    mapHom G F (𝟙 ξ) = 𝟙 (mapObj G F ξ) := by
  apply hom_ext_total (α := mapHom G F (𝟙 ξ)) (β := idHom (mapObj G F ξ)) rfl rfl
  · rfl
  · erw [mapHom_a_fac, idHom_a, CategoryTheory.Functor.map_id, idHom_a]
    rfl

/-- The induced map on finite Hilbert morphisms preserves composition. -/
theorem mapHom_comp (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ}
    {ξ ξ' ξ'' : Obj (G ≫ F) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    mapHom G F (φ ≫ ψ) = compHom (mapHom G F φ) (mapHom G F ψ) := by
  apply hom_ext_total (α := mapHom G F (φ ≫ ψ))
    (β := compHom (mapHom G F φ) (mapHom G F ψ)) rfl rfl
  · rfl
  · erw [mapHom_a_fac, compHom_a, CategoryTheory.Functor.map_comp, compHom_a,
      mapHom_a_fac, mapHom_a_fac]

end

/-- The total functor of the induced 1-morphism `H_d(X'/Y) ⟶ H_d(X/Y)`. -/
def mapFunctor (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) : Obj (G ≫ F) d ⥤ Obj F d where
  obj ξ := mapObj G F ξ
  map φ := mapHom G F φ
  map_id := mapHom_id G F
  map_comp := mapHom_comp G F

/-- `mapFunctor` lies strictly over the identity on test schemes. -/
theorem mapFunctor_p (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    mapFunctor G F d ⋙ p F d = p (G ≫ F) d := rfl

/-- The image of a quintuple under `mapFunctor` is obtained by applying the fibre
functor of `G` to the `X`-component and composing with `mapIso`. -/
theorem map_obj (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) (ξ : Obj (G ≫ F) d) :
    (mapFunctor G F d).obj ξ =
      Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree ξ.y
        ((fiberFunctor G ξ.Z).obj ξ.x) (ξ.iso ≪≫ mapIso G F ξ.x) := rfl

/-- `mapFunctor` preserves the underlying test scheme. -/
theorem map_U (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) (ξ : Obj (G ≫ F) d) :
    ((mapFunctor G F d).obj ξ).U = ξ.U := rfl

/-- The 1-morphism `H_d(X'/Y) ⟶ H_d(X/Y)` of categories fibred in groupoids
induced by `G : X' ⟶ X`. -/
def map (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    toGroupoids (G ≫ F) d ⟶ toGroupoids F d :=
  ofBasedFunctor (BasedFunctor.ofFunctor (mapFunctor G F d) (mapFunctor_p G F d))

/-- Forgetting `map` to based functors recovers `BasedFunctor.ofFunctor` of
`mapFunctor`. -/
theorem map.toBasedFunctor (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    toBasedFunctor (map G F d) =
      BasedFunctor.ofFunctor (mapFunctor G F d) (mapFunctor_p G F d) := rfl

end AlgebraicGeometry.FiniteHilbertStack
