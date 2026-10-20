/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.CategoryTheory.Cofibered.InGroupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Bundled predeformation categories and residue transport

Predeformation categories are bundled as categories cofibered in groupoids.
A morphism of groupoid fibrations induces a morphism of predeformation categories,
including transport along an isomorphism of the chosen residue objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- The predeformation category `ℱ_{𝒳, k, x₀}` as a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. -/
def bundled :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (predeformationFunctor X openImmersion kToS h_factor x0)

/-- The projection of `bundled X x0` is the forgetful functor of `ℱ_{𝒳, k, x₀}`. -/
theorem bundled_p :
    (bundled openImmersion kToS h_factor X x0).p =
      forget openImmersion kToS h_factor X x0 :=
  rfl

/-- Bundle the based functor `map φ x0` as a 1-morphism of categories cofibered in groupoids
over `ArtinianLocalAlgCat Λ k`. -/
def mapBundled {X Y : GroupoidsOver S} (φ : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion kToS h_factor Y (residueImage φ x0) :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor (map openImmersion h_factor φ x0)

/-- Forgetting `mapBundled` to based functors recovers `map`. -/
theorem mapBundled_toBasedFunctor {X Y : GroupoidsOver S} (φ : X ⟶ Y)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor φ x0) =
      map openImmersion h_factor φ x0 :=
  rfl

section MapAlong

variable {X Y : GroupoidsOver S} (φ : X ⟶ Y)
variable {x0 : X.p.Fiber (Over.mk kToS)} {y0 : Y.p.Fiber (Over.mk kToS)}
variable (α : residueImage φ x0 ≅ y0)

/-- Object map of `ℱ_{𝒳, k, x₀} → ℱ_{𝒴, k, y₀}` along a residue-fibre identification
`φ(x₀) ≅ y₀`. -/
def mapObjAlong (ξ : Obj openImmersion kToS h_factor X x0) :
    Obj openImmersion kToS h_factor Y y0 := by
  have compatibility : Y.p.IsHomLift
      (specOver_toResidue openImmersion kToS h_factor ξ.base)
      (Functor.Fiber.fiberInclusion.map α.inv ≫ (toFunctor φ).map ξ.fromResidue) := by
    sorry
  exact
    { base := ξ.base
      target := (fiberFunctor φ (specOver openImmersion ξ.base)).obj ξ.target
      fromResidue := Functor.Fiber.fiberInclusion.map α.inv ≫ (toFunctor φ).map ξ.fromResidue
      over_fromResidue := compatibility }

/-- The object map along a residue-fibre identification preserves the stored Artinian base. -/
theorem mapObjAlong_base (ξ : Obj openImmersion kToS h_factor X x0) :
    (mapObjAlong openImmersion kToS h_factor φ α ξ).base = ξ.base :=
  rfl

/-- Arrow map along a residue-fibre identification `φ(x₀) ≅ y₀`. -/
def mapHomAlong {ξ η : Obj openImmersion kToS h_factor X x0} (f : ξ ⟶ η) :
    mapObjAlong openImmersion kToS h_factor φ α ξ ⟶
      mapObjAlong openImmersion kToS h_factor φ α η := by
  have compatibility :
      Y.p.IsHomLift (specOverMap openImmersion f.baseHom) ((toFunctor φ).map f.hom) ∧
        (mapObjAlong openImmersion kToS h_factor φ α ξ).fromResidue =
          (mapObjAlong openImmersion kToS h_factor φ α η).fromResidue ≫
            (toFunctor φ).map f.hom := by
    sorry
  exact
    { baseHom := f.baseHom
      hom := (toFunctor φ).map f.hom
      over_hom := compatibility.1
      triangle := compatibility.2 }

/-- The functor `ℱ_{𝒳, k, x₀} ⥤ ℱ_{𝒴, k, y₀}` along a residue-fibre identification. -/
def mapFunctorAlong : Obj openImmersion kToS h_factor X x0 ⥤
    Obj openImmersion kToS h_factor Y y0 := by
  have laws :
      (∀ ξ : Obj openImmersion kToS h_factor X x0,
        mapHomAlong openImmersion kToS h_factor φ α (𝟙 ξ) =
          𝟙 (mapObjAlong openImmersion kToS h_factor φ α ξ)) ∧
      (∀ (ξ η ζ : Obj openImmersion kToS h_factor X x0) (f : ξ ⟶ η) (g : η ⟶ ζ),
        mapHomAlong openImmersion kToS h_factor φ α (f ≫ g) =
          mapHomAlong openImmersion kToS h_factor φ α f ≫
            mapHomAlong openImmersion kToS h_factor φ α g) := by
    sorry
  exact
    { obj ξ := mapObjAlong openImmersion kToS h_factor φ α ξ
      map f := mapHomAlong openImmersion kToS h_factor φ α f
      map_id := laws.1
      map_comp := fun f g => laws.2 _ _ _ f g }

/-- `mapFunctorAlong` lies strictly over `ArtinianLocalAlgCat Λ k`. -/
def mapBasedFunctorAlong :
    BasedCategory.ofFunctor (forget openImmersion kToS h_factor X x0) ⥤ᵇ
      BasedCategory.ofFunctor (forget openImmersion kToS h_factor Y y0) := by
  have compatibility :
      mapFunctorAlong openImmersion kToS h_factor φ α ⋙
          forget openImmersion kToS h_factor Y y0 =
        forget openImmersion kToS h_factor X x0 := by
    sorry
  exact BasedFunctor.ofFunctor (mapFunctorAlong openImmersion kToS h_factor φ α) compatibility

/-- The 1-morphism of predeformation categories along a residue-fibre identification. -/
def mapAlong : bundled openImmersion kToS h_factor X x0 ⟶
    bundled openImmersion kToS h_factor Y y0 :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor
    (mapBasedFunctorAlong openImmersion kToS h_factor φ α)

/-- Forgetting `mapAlong` to based functors recovers `mapBasedFunctorAlong`. -/
theorem mapAlong_toBasedFunctor :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapAlong openImmersion kToS h_factor φ α) =
      mapBasedFunctorAlong openImmersion kToS h_factor φ α :=
  rfl

end MapAlong

end AlgebraicGeometry.GroupoidsOver.Predeformation
