module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Category of schemes flat over objects of `ArtinianLocalAlgCat`

Objects are pairs `(A, X)` with `A` in `ArtinianLocalAlgCat` and `X` a scheme
flat over `A`. Morphisms are pairs `(f, g)` whose associated Spec-square is
cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

noncomputable section

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- An object of the category `F` of pairs `(A, X)` with `A` in `C_Λ` and `X` a
scheme flat over `A`. -/
structure FlatSchemeCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying scheme. -/
  scheme : Scheme.{u}
  /-- Structure morphism exhibiting the scheme as a scheme over the base. -/
  structureHom : scheme ⟶ Spec (CommRingCat.of base.carrier)
  /-- The structure morphism is flat. -/
  [isFlat : AlgebraicGeometry.Flat structureHom]

attribute [instance] FlatSchemeCat.isFlat

namespace FlatSchemeCat

variable {Λ k}

/-- Pair an Artinian local algebra with a scheme flat over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (X : Scheme.{u})
    (structureHom : X ⟶ Spec (CommRingCat.of A.carrier))
    [AlgebraicGeometry.Flat structureHom] : FlatSchemeCat Λ k where
  base := A
  scheme := X
  structureHom := structureHom

/-- An object of `F` is a pair `(A, X)` with `X` flat over `A`. -/
theorem spec (P : FlatSchemeCat Λ k) :
    AlgebraicGeometry.Flat P.structureHom := sorry

/-- The morphism of spectra associated with a morphism of `C_Λ`. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Spec (CommRingCat.of B.carrier) ⟶ Spec (CommRingCat.of A.carrier) :=
  Spec.map (CommRingCat.ofHom f.hom.toRingHom)

/-- `specMap` sends identity morphisms of `C_Λ` to identity morphisms of spectra. -/
theorem specMap_id (A : ArtinianLocalAlgCat Λ k) :
    specMap (𝟙 A) = 𝟙 (Spec (CommRingCat.of A.carrier)) := sorry

/-- `specMap` is contravariant on morphisms of `C_Λ`. -/
theorem specMap_comp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    specMap (f ≫ g) = specMap g ≫ specMap f := sorry

/-- A morphism `(f, g) : (B, Y) ⟶ (A, X)` is a morphism `f : B ⟶ A` in `C_Λ`
together with a morphism `g : X ⟶ Y` making a cartesian Spec-square. -/
structure Hom (src tgt : FlatSchemeCat Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  baseHom : src.base ⟶ tgt.base
  /-- Underlying morphism of schemes, pointing toward the source scheme. -/
  schemeHom : tgt.scheme ⟶ src.scheme
  /-- The associated Spec-square is cartesian. -/
  isPullback :
    IsPullback schemeHom tgt.structureHom src.structureHom (specMap baseHom)

namespace Hom

/-- Package a base morphism and a scheme morphism forming a cartesian Spec-square. -/
def of {src tgt : FlatSchemeCat Λ k} (baseHom : src.base ⟶ tgt.base)
    (schemeHom : tgt.scheme ⟶ src.scheme)
    (isPullback :
      IsPullback schemeHom tgt.structureHom src.structureHom (specMap baseHom)) :
    Hom src tgt where
  baseHom := baseHom
  schemeHom := schemeHom
  isPullback := isPullback

/-- Identity morphism of a pair `(A, X)`. -/
def id (P : FlatSchemeCat Λ k) : Hom P P where
  baseHom := 𝟙 P.base
  schemeHom := 𝟙 P.scheme
  isPullback := sorry

/-- Composition of morphisms of pairs. -/
def comp {src mid tgt : FlatSchemeCat Λ k} (f : Hom src mid) (g : Hom mid tgt) :
    Hom src tgt where
  baseHom := f.baseHom ≫ g.baseHom
  schemeHom := g.schemeHom ≫ f.schemeHom
  isPullback := sorry

/-- A morphism is a cartesian commutative Spec-square. -/
theorem spec {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) :
    f.schemeHom ≫ src.structureHom = tgt.structureHom ≫ specMap f.baseHom ∧
      IsPullback f.schemeHom tgt.structureHom src.structureHom (specMap f.baseHom) :=
  sorry

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (P : FlatSchemeCat Λ k) : (id P).baseHom = 𝟙 P.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_baseHom {src mid tgt : FlatSchemeCat Λ k} (f : Hom src mid)
    (g : Hom mid tgt) : (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

end Hom

/-- Category of pairs `(A, X)` with cartesian Spec-squares as morphisms. -/
instance category : Category.{u} (FlatSchemeCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

section Forget

variable (Λ k)

/-- The functor `p` sending `(A, X)` to `A` and `(f, g)` to `f`. -/
def forget : FlatSchemeCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj P := P.base
  map f := f.baseHom
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (P : FlatSchemeCat Λ k) : (forget Λ k).obj P = P.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt) :
    (forget Λ k).map f = f.baseHom := sorry

/-- The projection `p : F ⥤ C_Λ` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Λ k).op := sorry

end Forget

end FlatSchemeCat
