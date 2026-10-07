module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Category of flat algebraic spaces over `ArtinianLocalAlgCat`

Objects are pairs `(A, X)` with `A` in `ArtinianLocalAlgCat` and `X` an algebraic
space flat over `A`. Morphisms are pairs `(f, g)` whose `Spec`-square is cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Functor

noncomputable section

universe u

namespace FlatAlgebraicSpaceCat

/-- The spectrum of `Λ`, viewed as the standing base scheme. -/
abbrev specBase (Λ : Type u) [CommRing Λ] : Scheme.{u} :=
  Spec (CommRingCat.of Λ)

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- `Spec(A)` as a scheme over `Spec(Λ)`. -/
def specHom (A : ArtinianLocalAlgCat Λ k) :
    Spec (CommRingCat.of A.carrier) ⟶ specBase Λ :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier))

/-- `specHom A` is `Spec` of the structure map `Λ → A`. -/
theorem specHom_eq (A : ArtinianLocalAlgCat Λ k) :
    specHom A = Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) := sorry

/-- `Spec(A)` as an algebraic space over `Λ`. -/
def specObj (A : ArtinianLocalAlgCat Λ k) : AlgebraicSpace (specBase Λ) :=
  ofOver (Over.mk (specHom A))

/-- `specObj A` is the algebraic space represented by `Spec(A)` over `Spec(Λ)`. -/
theorem specObj_eq (A : ArtinianLocalAlgCat Λ k) :
    specObj A = ofOver (Over.mk (specHom A)) := sorry

/-- A morphism `f : A ⟶ B` in `C_Λ` is compatible with the structure maps from `Λ`. -/
theorem specMap_w {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ specHom A = specHom B := sorry

/-- The contravariant `Spec` map of a morphism in `C_Λ`, as a morphism of algebraic
spaces over `Λ`. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specObj B ⟶ specObj A :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (specMap_w f)

/-- `specMap f` is `ofOverHomMk` of `Spec.map` of the underlying ring map. -/
theorem specMap_eq {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specMap f = ofOverHomMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (specMap_w f) :=
  sorry

end FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

open FlatAlgebraicSpaceCat (specBase specObj specMap)

/-- An object of the category `F` of pairs `(A, X)` with `A` in `C_Λ` and `X` an
algebraic space flat over `A`. -/
structure FlatAlgebraicSpaceCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying algebraic space over `Spec(Λ)`. -/
  space : AlgebraicSpace (specBase Λ)
  /-- Structure morphism `X ⟶ Spec(A)` of algebraic spaces over `Λ`. -/
  structureHom : space ⟶ specObj base
  /-- The structure morphism is flat. -/
  [isFlat : AlgebraicSpace.Flat structureHom]

attribute [instance] FlatAlgebraicSpaceCat.isFlat

namespace FlatAlgebraicSpaceCat

variable {Λ k}

/-- Pair an Artinian local algebra with an algebraic space flat over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (X : AlgebraicSpace (specBase Λ))
    (structureHom : X ⟶ specObj A) (hflat : AlgebraicSpace.Flat structureHom) :
    FlatAlgebraicSpaceCat Λ k where
  base := A
  space := X
  structureHom := structureHom
  isFlat := hflat

/-- The constructor recovers the supplied base, algebraic space, structure morphism,
and flatness. -/
theorem of_spec (A : ArtinianLocalAlgCat Λ k) (X : AlgebraicSpace (specBase Λ))
    (structureHom : X ⟶ specObj A) (hflat : AlgebraicSpace.Flat structureHom) :
    (of A X structureHom hflat).base = A ∧
      (of A X structureHom hflat).space = X ∧
      (of A X structureHom hflat).structureHom = structureHom ∧
      AlgebraicSpace.Flat (of A X structureHom hflat).structureHom := sorry

/-- An object of `F` is an algebraic space flat over its stored base in `C_Λ`. -/
theorem spec (X : FlatAlgebraicSpaceCat Λ k) : AlgebraicSpace.Flat X.structureHom := sorry

/-- A morphism `(f, g) : (B, Y) ⟶ (A, X)` in `F`: a map `f : B ⟶ A` in `C_Λ` and a
map `g : X ⟶ Y` of algebraic spaces over `Λ` making the `Spec`-square cartesian. -/
structure Hom (Y X : FlatAlgebraicSpaceCat Λ k) where
  /-- Underlying morphism `B ⟶ A` in `ArtinianLocalAlgCat`. -/
  baseHom : Y.base ⟶ X.base
  /-- Underlying morphism `X ⟶ Y` of algebraic spaces over `Λ`. -/
  spaceHom : X.space ⟶ Y.space
  /-- The square with `Spec(A) ⟶ Spec(B)` is a pullback of algebraic spaces. -/
  isPullback : IsPullback spaceHom X.structureHom Y.structureHom (specMap baseHom)

namespace Hom

/-- Package a base morphism and an opposite space morphism whose `Spec`-square is
cartesian. -/
def of {Y X : FlatAlgebraicSpaceCat Λ k} (baseHom : Y.base ⟶ X.base)
    (spaceHom : X.space ⟶ Y.space)
    (isPullback : IsPullback spaceHom X.structureHom Y.structureHom (specMap baseHom)) :
    Hom Y X where
  baseHom := baseHom
  spaceHom := spaceHom
  isPullback := isPullback

/-- Identity morphism of a pair `(A, X)`. -/
def id (X : FlatAlgebraicSpaceCat Λ k) : Hom X X where
  baseHom := 𝟙 X.base
  spaceHom := 𝟙 X.space
  isPullback := sorry

/-- Composition of morphisms of pairs. -/
def comp {X Y Z : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  baseHom := f.baseHom ≫ g.baseHom
  spaceHom := g.spaceHom ≫ f.spaceHom
  isPullback := sorry

/-- A morphism is a pair `(f, g)` whose `Spec`-square is cartesian. -/
theorem spec {Y X : FlatAlgebraicSpaceCat Λ k} (f : Hom Y X) :
    IsPullback f.spaceHom X.structureHom Y.structureHom (specMap f.baseHom) ∧
      f.spaceHom ≫ Y.structureHom = X.structureHom ≫ specMap f.baseHom := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_baseHom (X : FlatAlgebraicSpaceCat Λ k) : (id X).baseHom = 𝟙 X.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_baseHom {X Y Z : FlatAlgebraicSpaceCat Λ k} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

end Hom

/-- Category of pairs `(A, X)` with cartesian morphisms of algebraic spaces over `Λ`. -/
instance category : Category.{u + 1} (FlatAlgebraicSpaceCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

variable (Λ k)

/-- The functor `p` sending `(A, X)` to `A` and `(f, g)` to `f`. -/
def forget : FlatAlgebraicSpaceCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.baseHom
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : FlatAlgebraicSpaceCat Λ k) : (forget Λ k).obj X = X.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {Y X : FlatAlgebraicSpaceCat Λ k} (f : Y ⟶ X) :
    (forget Λ k).map f = f.baseHom := sorry

/-- The projection `p : F ⥤ C_Λ` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Λ k).op := sorry

end FlatAlgebraicSpaceCat

