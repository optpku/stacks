module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import stacks_project.Chap98.«98_3_0_2_Category»

/-!
# Functoriality of CFG-associated predeformation categories

A 1-morphism of categories fibred in groupoids over `Over S` induces a based functor
between the associated categories `ℱ_{X, k, x0}` and `ℱ_{Y, k, y0}` over
`ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor fiberFunctor)

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}

/-- The object `y0 = F(x0)` in the fibre of `Y` over `Over.mk kToS`. -/
def residueImage (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    Y.p.Fiber (Over.mk kToS) :=
  (fiberFunctor F (Over.mk kToS)).obj x0

/-- `residueImage F x0` is the image of `x0` under the total functor of `F`. -/
theorem residueImage_obj (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.Fiber.fiberInclusion.obj (residueImage F x0) =
      (toFunctor F).obj (Functor.Fiber.fiberInclusion.obj x0) :=
  sorry

/-- The category `ℱ_{X, k, x0}` as a based category over `ArtinianLocalAlgCat Λ k`. -/
abbrev predeformation (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (x0 : X.p.Fiber (Over.mk kToS)) : BasedCategory (ArtinianLocalAlgCat Λ k) :=
  BasedCategory.ofFunctor (forget openImmersion kToS h_factor X x0)

/-- The projection of `predeformation X x0` is the forgetful functor to
`ArtinianLocalAlgCat Λ k`. -/
theorem predeformation_p
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (x0 : X.p.Fiber (Over.mk kToS)) :
    (predeformation openImmersion h_factor X x0).p =
      forget openImmersion kToS h_factor X x0 :=
  sorry

/-- The object `F(x0) ⟶ F(x)` associated to an object `x0 ⟶ x` of `ℱ_{X, k, x0}`. -/
def mapObj (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    Obj openImmersion kToS h_factor Y (residueImage F x0) where
  base := ξ.base
  target := (fiberFunctor F (specOver openImmersion ξ.base)).obj ξ.target
  fromResidue := (toFunctor F).map ξ.fromResidue
  over_fromResidue := sorry

/-- The reversed triangle `F(x') ⟶ F(x)` associated to a morphism of `ℱ_{X, k, x0}`. -/
def mapHom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    Hom (mapObj openImmersion h_factor F x0 ξ) (mapObj openImmersion h_factor F x0 η) where
  baseHom := f.baseHom
  hom := (toFunctor F).map f.hom
  over_hom := sorry
  triangle := sorry

/-- A 1-morphism `F : X ⟶ Y` induces a based functor `ℱ_{X, k, x0} ⥤ᵇ ℱ_{Y, k, y0}`
over `ArtinianLocalAlgCat Λ k`, where `y0` is `residueImage F x0`. -/
def map (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    predeformation openImmersion h_factor X x0 ⥤ᵇ
      predeformation openImmersion h_factor Y (residueImage F x0) where
  obj := mapObj openImmersion h_factor F x0
  map f := mapHom openImmersion h_factor F x0 f
  map_id := sorry
  map_comp := sorry
  w := sorry

/-- `map F x0` preserves the Artinian local algebra underlying an object. -/
theorem map_obj_base (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).base = ξ.base :=
  sorry

/-- `map F x0` sends the target object `x` to its image under `fiberFunctor F`. -/
theorem map_obj_target (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).target =
      (fiberFunctor F (specOver openImmersion ξ.base)).obj ξ.target :=
  sorry

/-- `map F x0` sends the morphism `x0 ⟶ x` to `F(x0) ⟶ F(x)`. -/
theorem map_obj_fromResidue (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).fromResidue =
      (toFunctor F).map ξ.fromResidue :=
  sorry

/-- `map F x0` preserves the underlying morphism of Artinian local algebras. -/
theorem map_map_baseHom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    ((map openImmersion h_factor F x0).map f).baseHom = f.baseHom :=
  sorry

/-- The reversed arrow of `map F x0` is `toFunctor F` applied to the source arrow. -/
theorem map_map_hom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    ((map openImmersion h_factor F x0).map f).hom = (toFunctor F).map f.hom :=
  sorry

/-- `map F x0` is a morphism of categories over `ArtinianLocalAlgCat Λ k`. -/
theorem map_forget (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    (map openImmersion h_factor F x0).toFunctor ⋙
        forget openImmersion kToS h_factor Y (residueImage F x0) =
      forget openImmersion kToS h_factor X x0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
