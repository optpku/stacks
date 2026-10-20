/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Restriction of a based category over `Ĉ_Λ` along `C_Λ ↪ Ĉ_Λ`

Objects of `BasedCategory.RestrictInclusion X` are objects of a based category `X` over
`CompleteLocalAlgCat Λ k` whose base is the image of an Artinian algebra. This is the
strict pullback of `X.p` along `ArtinianLocalAlgCat.inclusion`.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedCategory

/-- An object of `X` lying strictly over the image of an Artinian algebra under
`ArtinianLocalAlgCat.inclusion`. -/
def RestrictInclusion
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :=
  Σ' obj : X.obj, Σ' base : ArtinianLocalAlgCat Λ k, X.p.obj obj = toComplete base

namespace RestrictInclusion

variable {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- The underlying object of a restriction. -/
def obj (ξ : RestrictInclusion X) : X.obj := ξ.1
/-- The Artinian base of a restriction. -/
def base (ξ : RestrictInclusion X) : ArtinianLocalAlgCat Λ k := ξ.2.1
/-- The stored projection identification. -/
theorem over (ξ : RestrictInclusion X) : X.p.obj ξ.obj = toComplete ξ.base := ξ.2.2

/-- Package an object of `X` lying over `toComplete A` as a restricted object. -/
def of (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) : RestrictInclusion X := ⟨obj, base, over⟩

/-- The underlying object of a packaged restriction is the supplied object. -/
theorem of_obj (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).obj = obj := rfl

/-- The Artinian base of a packaged restriction is the supplied algebra. -/
theorem of_base (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).base = base := rfl

/-- A restricted object lies over `toComplete` of its Artinian base. -/
theorem spec (ξ : RestrictInclusion X) : X.p.obj ξ.obj = toComplete ξ.base := ξ.over

/-- A morphism of restricted objects is an arrow together with a compatible Artinian base map. -/
def Hom (ξ η : RestrictInclusion X) :=
  Σ' obj : ξ.obj ⟶ η.obj, Σ' base : ξ.base ⟶ η.base,
    inclusion.map base = eqToHom ξ.over.symm ≫ X.p.map obj ≫ eqToHom η.over

private def categoricalHom (ξ η : RestrictInclusion X) := Hom ξ η

/-- The underlying arrow of a restricted morphism. -/
def Hom.obj {ξ η : RestrictInclusion X} (a : Hom ξ η) : ξ.obj ⟶ η.obj := a.1
/-- The base arrow of a restricted morphism. -/
def Hom.base {ξ η : RestrictInclusion X} (a : Hom ξ η) : ξ.base ⟶ η.base := a.2.1
/-- The compatibility of a restricted morphism with its projection. -/
theorem Hom.over {ξ η : RestrictInclusion X} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ X.p.map a.obj ≫ eqToHom η.over := a.2.2
/-- Construct a morphism from its compatible components. -/
def Hom.of {ξ η : RestrictInclusion X} (obj : ξ.obj ⟶ η.obj) (base : ξ.base ⟶ η.base)
    (over : inclusion.map base = eqToHom ξ.over.symm ≫ X.p.map obj ≫ eqToHom η.over) :
    Hom ξ η := ⟨obj, base, over⟩

/-- The identity arrows satisfy the compatibility with the base projection. -/
theorem Hom.id_laws (ξ : RestrictInclusion X) :
    inclusion.map (𝟙 ξ.base) = eqToHom ξ.over.symm ≫ X.p.map (𝟙 ξ.obj) ≫ eqToHom ξ.over := sorry

/-- Identity morphism of a restricted object. -/
def Hom.id (ξ : RestrictInclusion X) : Hom ξ ξ :=
  Hom.of (𝟙 ξ.obj) (𝟙 ξ.base) (Hom.id_laws ξ)

/-- Composition preserves compatibility with the base projection. -/
theorem Hom.comp_laws {ξ η ζ : RestrictInclusion X} (a : Hom ξ η) (b : Hom η ζ) :
    inclusion.map (a.base ≫ b.base) =
      eqToHom ξ.over.symm ≫ X.p.map (a.obj ≫ b.obj) ≫ eqToHom ζ.over := sorry

/-- Composition of morphisms of restricted objects. -/
def Hom.comp {ξ η ζ : RestrictInclusion X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ :=
  Hom.of (a.obj ≫ b.obj) (a.base ≫ b.base) (Hom.comp_laws a b)

/-- A restricted morphism is compatible with inclusion of Artinian bases. -/
theorem Hom.spec {ξ η : RestrictInclusion X} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ X.p.map a.obj ≫ eqToHom η.over := a.over

/-- Restricted identities and composition satisfy the category laws. -/
theorem category_laws :
    (∀ (ξ η : RestrictInclusion X) (f : Hom ξ η), Hom.comp (Hom.id ξ) f = f) ∧
    (∀ (ξ η : RestrictInclusion X) (f : Hom ξ η), Hom.comp f (Hom.id η) = f) ∧
    (∀ (ξ η ζ θ : RestrictInclusion X) (f : Hom ξ η) (g : Hom η ζ) (h : Hom ζ θ),
      Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) := sorry

private abbrev categoricalStructure : Category.{max u v} (RestrictInclusion X) where
  Hom := categoricalHom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := category_laws.1 _ _
  comp_id := category_laws.2.1 _ _
  assoc := category_laws.2.2 _ _ _ _

/-- Category of objects of `X` restricted to Artinian bases. -/
instance category : Category.{max u v} (RestrictInclusion X) := categoricalStructure

/-- Projection of restricted arrows preserves identities and composition. -/
theorem projection_laws :
    (∀ ξ : RestrictInclusion X, Hom.base (𝟙 ξ) = 𝟙 ξ.base) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      Hom.base (f ≫ g) = f.base ≫ g.base) := sorry

/-- The projection `X|_{C_Λ} ⥤ C_Λ` sending a restricted object to its Artinian base. -/
def projection (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := projection_laws.1
  map_comp := projection_laws.2 _ _ _

/-- The projection sends a restricted object to its stored Artinian base. -/
theorem projection_obj (ξ : RestrictInclusion X) :
    (projection X).obj ξ = ξ.base := rfl

/-- The underlying arrows of restrictions preserve identities and composition. -/
theorem ι_laws :
    (∀ ξ : RestrictInclusion X, Hom.obj (𝟙 ξ) = 𝟙 ξ.obj) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      Hom.obj (f ≫ g) = f.obj ≫ g.obj) := sorry

/-- Inclusion of the restriction into the total category of `X`. -/
def ι (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ X.obj where
  obj ξ := ξ.obj
  map a := a.obj
  map_id := ι_laws.1
  map_comp := ι_laws.2 _ _ _

/-- The inclusion sends a restricted object to its stored object of `X`. -/
theorem ι_obj (ξ : RestrictInclusion X) : (ι X).obj ξ = ξ.obj := rfl

/-- The restricted projection is cofibered in groupoids. -/
instance projection_op_isFiberedInGroupoids
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k))
    [Functor.IsFibered.InGroupoids X.p.op] :
    Functor.IsFibered.InGroupoids (projection X).op := sorry

variable {Y : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- Applying a based functor preserves the compatibility of a restricted arrow. -/
theorem mapFunctor_over (φ : X ⥤ᵇ Y) {ξ η : RestrictInclusion X} (a : ξ ⟶ η) :
    inclusion.map a.base =
      eqToHom ((BasedFunctor.w_obj φ ξ.obj).trans ξ.over).symm ≫
        Y.p.map (φ.map a.obj) ≫ eqToHom ((BasedFunctor.w_obj φ η.obj).trans η.over) := sorry
private def mapFunctorObj (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) : RestrictInclusion Y :=
  of (φ.obj ξ.obj) ξ.base ((BasedFunctor.w_obj φ ξ.obj).trans ξ.over)
private def mapFunctorMap (φ : X ⥤ᵇ Y) {ξ η : RestrictInclusion X} (a : ξ ⟶ η) :
    mapFunctorObj φ ξ ⟶ mapFunctorObj φ η :=
  Hom.of (φ.map a.obj) a.base (mapFunctor_over φ a)
/-- Restriction of a based functor preserves identities and composition. -/
theorem mapFunctor_laws (φ : X ⥤ᵇ Y) :
    (∀ ξ, mapFunctorMap φ (𝟙 ξ) = 𝟙 (mapFunctorObj φ ξ)) ∧
    (∀ (ξ η ζ : RestrictInclusion X) (f : ξ ⟶ η) (g : η ⟶ ζ),
      mapFunctorMap φ (f ≫ g) = mapFunctorMap φ f ≫ mapFunctorMap φ g) := sorry
/-- Apply a based functor to the underlying objects and arrows of the restriction. -/
def mapFunctor (φ : X ⥤ᵇ Y) : RestrictInclusion X ⥤ RestrictInclusion Y where
  obj := mapFunctorObj φ
  map := mapFunctorMap φ
  map_id := (mapFunctor_laws φ).1
  map_comp := (mapFunctor_laws φ).2 _ _ _

/-- Mapping a restricted object along `φ` preserves the Artinian base. -/
theorem mapFunctor_obj_base (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).base = ξ.base := rfl

/-- Mapping a restricted object along `φ` applies `φ` to the underlying object. -/
theorem map_obj (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).obj = φ.obj ξ.obj := rfl

/-- The induced functor commutes with the Artinian projections. -/
theorem map_w (φ : X ⥤ᵇ Y) : mapFunctor φ ⋙ projection Y = projection X := sorry
/-- Restriction of a based functor as a based functor. -/
def map (φ : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (projection X) ⥤ᵇ BasedCategory.ofFunctor (projection Y) where
  toFunctor := mapFunctor φ
  w := map_w φ

/-- Restriction of a vertical transformation is natural and vertical. -/
theorem map₂_laws {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) :
    (∀ ξ : RestrictInclusion X,
      inclusion.map (𝟙 ξ.base) =
        eqToHom ((mapFunctor φ).obj ξ).over.symm ≫ Y.p.map (t.toNatTrans.app ξ.obj) ≫
          eqToHom ((mapFunctor ψ).obj ξ).over) ∧
    (∀ (h : ∀ ξ : RestrictInclusion X,
      inclusion.map (𝟙 ξ.base) =
        eqToHom ((mapFunctor φ).obj ξ).over.symm ≫ Y.p.map (t.toNatTrans.app ξ.obj) ≫
          eqToHom ((mapFunctor ψ).obj ξ).over),
      (∀ (ξ η : RestrictInclusion X) (a : ξ ⟶ η),
        (mapFunctor φ).map a ≫
          Hom.of (ξ := (mapFunctor φ).obj η) (η := (mapFunctor ψ).obj η)
            (t.toNatTrans.app η.obj) (𝟙 η.base) (h η) =
          Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
            (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) (h ξ) ≫ (mapFunctor ψ).map a) ∧
      (∀ ξ : RestrictInclusion X, (projection Y).IsHomLift (𝟙 ξ.base)
        (Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
          (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) (h ξ)))) := sorry
/-- Restriction of a vertical natural transformation. -/
def map₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : map φ ⟶ map ψ where
  toNatTrans :=
    { app ξ := Hom.of (ξ := (mapFunctor φ).obj ξ) (η := (mapFunctor ψ).obj ξ)
        (t.toNatTrans.app ξ.obj) (𝟙 ξ.base) ((map₂_laws t).1 ξ)
      naturality := fun {ξ η} a ↦ ((map₂_laws t).2 (map₂_laws t).1).1 ξ η a }
  isHomLift' := ((map₂_laws t).2 (map₂_laws t).1).2

/-- The stage-object component of a mapped `2`-cell is the component of `t`. -/
theorem map₂_app (φ ψ : X ⥤ᵇ Y) (t : φ ⟶ ψ) (ξ : RestrictInclusion X) :
    ((map₂ t).toNatTrans.app ξ).obj = t.toNatTrans.app ξ.obj := rfl

end RestrictInclusion

end CategoryTheory.BasedCategory

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

/-- Restriction of a category cofibered in groupoids over `Ĉ_Λ` along
`ArtinianLocalAlgCat.inclusion`, as a category cofibered in groupoids over `C_Λ`. -/
def restrictInclusion
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)) :
    CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (ArtinianLocalAlgCat Λ k) :=
  ofFunctor (BasedCategory.RestrictInclusion.projection G.toBasedCategory)

/-- The projection of the bundled restriction is the restricted projection. -/
theorem restrictInclusion_p
    (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k)) :
    (restrictInclusion G).p =
      BasedCategory.RestrictInclusion.projection G.toBasedCategory := rfl

end CategoryTheory.CofiberedCategoryOver.Groupoids
