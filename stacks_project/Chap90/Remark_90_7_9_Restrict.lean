module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Remark_90_7_8_Groupoids

/-!
# Restriction of a based category over `Ĉ_Λ` along `C_Λ ↪ Ĉ_Λ`

Objects of `BasedCategory.RestrictInclusion X` are objects of a based category `X` over
`CompleteLocalAlgCat Λ k` whose base is the image of an Artinian algebra. This is the
strict pullback of `X.p` along `ArtinianLocalAlgCat.inclusion`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedCategory

/-- An object of `X` lying strictly over the image of an Artinian algebra under
`ArtinianLocalAlgCat.inclusion`. -/
structure RestrictInclusion
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) where
  /-- Underlying object of `X`. -/
  obj : X.obj
  /-- Artinian base of the restricted object. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The object lies over the complete-local view of `base`. -/
  over : X.p.obj obj = toComplete base

namespace RestrictInclusion

variable {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- Package an object of `X` lying over `toComplete A` as a restricted object. -/
def of (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) : RestrictInclusion X where
  obj := obj
  base := base
  over := over

/-- The underlying object of a packaged restriction is the supplied object. -/
theorem of_obj (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).obj = obj := sorry

/-- The Artinian base of a packaged restriction is the supplied algebra. -/
theorem of_base (obj : X.obj) (base : ArtinianLocalAlgCat Λ k)
    (over : X.p.obj obj = toComplete base) :
    (of obj base over).base = base := sorry

/-- A restricted object lies over `toComplete` of its Artinian base. -/
theorem spec (ξ : RestrictInclusion X) : X.p.obj ξ.obj = toComplete ξ.base := sorry

/-- A morphism of restricted objects is a morphism of `X` together with an Artinian base
map compatible with inclusion into complete local algebras. -/
structure Hom (ξ η : RestrictInclusion X) where
  /-- Underlying morphism in `X`. -/
  obj : ξ.obj ⟶ η.obj
  /-- Underlying morphism of Artinian bases. -/
  base : ξ.base ⟶ η.base
  /-- The complete-local view of `base` recovers the projection of `obj`. -/
  over : inclusion.map base = eqToHom ξ.over.symm ≫ X.p.map obj ≫ eqToHom η.over

/-- Identity morphism of a restricted object. -/
def Hom.id (ξ : RestrictInclusion X) : Hom ξ ξ where
  obj := 𝟙 ξ.obj
  base := 𝟙 ξ.base
  over := sorry

/-- Composition of morphisms of restricted objects. -/
def Hom.comp {ξ η ζ : RestrictInclusion X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  obj := a.obj ≫ b.obj
  base := a.base ≫ b.base
  over := sorry

/-- A restricted morphism is compatible with inclusion of Artinian bases. -/
theorem Hom.spec {ξ η : RestrictInclusion X} (a : Hom ξ η) :
    inclusion.map a.base = eqToHom ξ.over.symm ≫ X.p.map a.obj ≫ eqToHom η.over := sorry

/-- Category of objects of `X` restricted to `C_Λ`. -/
instance category : Category.{max u v} (RestrictInclusion X) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection `X|_{C_Λ} ⥤ C_Λ` sending a restricted object to its Artinian base. -/
def projection (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := sorry
  map_comp := sorry

/-- The projection sends a restricted object to its stored Artinian base. -/
theorem projection_obj (ξ : RestrictInclusion X) :
    (projection X).obj ξ = ξ.base := sorry

/-- Inclusion of the restriction into the total category of `X`. -/
def ι (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    RestrictInclusion X ⥤ X.obj where
  obj ξ := ξ.obj
  map a := a.obj
  map_id := sorry
  map_comp := sorry

/-- The inclusion sends a restricted object to its stored object of `X`. -/
theorem ι_obj (ξ : RestrictInclusion X) : (ι X).obj ξ = ξ.obj := sorry

/-- The restricted projection is cofibered in groupoids. -/
instance projection_op_isFiberedInGroupoids
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k))
    [Functor.IsFibered.InGroupoids X.p.op] :
    Functor.IsFibered.InGroupoids (projection X).op := sorry

variable {Y : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- The functor on restricted objects induced by a based functor over `Ĉ_Λ`. -/
def mapFunctor (φ : X ⥤ᵇ Y) : RestrictInclusion X ⥤ RestrictInclusion Y where
  obj ξ := of (φ.obj ξ.obj) ξ.base ((BasedFunctor.w_obj φ ξ.obj).trans ξ.over)
  map a :=
    { obj := φ.map a.obj
      base := a.base
      over := sorry }
  map_id := sorry
  map_comp := sorry

/-- Mapping a restricted object along `φ` preserves the Artinian base. -/
theorem mapFunctor_obj_base (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).base = ξ.base := sorry

/-- Mapping a restricted object along `φ` applies `φ` to the underlying object. -/
theorem map_obj (φ : X ⥤ᵇ Y) (ξ : RestrictInclusion X) :
    ((mapFunctor φ).obj ξ).obj = φ.obj ξ.obj := sorry

/-- The based functor of restrictions over `C_Λ` induced by a based functor over `Ĉ_Λ`. -/
def map (φ : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (projection X) ⥤ᵇ BasedCategory.ofFunctor (projection Y) where
  toFunctor := mapFunctor φ
  w := sorry

/-- The induced based functor of restrictions lies over the identity of `C_Λ`. -/
theorem map_w (φ : X ⥤ᵇ Y) :
    (map φ).toFunctor ⋙ projection Y = projection X := sorry

/-- The natural transformation of restricted functors induced by a based `2`-morphism. -/
def map₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : map φ ⟶ map ψ where
  toNatTrans :=
    { app ξ :=
        { obj := t.toNatTrans.app ξ.obj
          base := 𝟙 ξ.base
          over := sorry }
      naturality := sorry }
  isHomLift' := sorry

/-- The stage-object component of a mapped `2`-cell is the component of `t`. -/
theorem map₂_app (φ ψ : X ⥤ᵇ Y) (t : φ ⟶ ψ) (ξ : RestrictInclusion X) :
    ((map₂ t).toNatTrans.app ξ).obj = t.toNatTrans.app ξ.obj := sorry

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
      BasedCategory.RestrictInclusion.projection G.toBasedCategory := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids
