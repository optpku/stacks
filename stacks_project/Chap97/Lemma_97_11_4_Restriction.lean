module

public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom

/-!
# Restriction of scalars of algebraic spaces

The sheaf `Res_{Z/B}(X)` on the fppf site of schemes over `S`, whose value at `T`
is a morphism `a : T ⟶ B` together with a morphism `T ×_B Z ⟶ X` over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

variable {S : Scheme.{u}} {X Z B : AlgebraicSpace S}

/-- A `T`-point of `Res_{Z/B}(X)`: a morphism `a : T ⟶ B` and a morphism
`b : T ×_B Z ⟶ X` over `Z`. -/
structure Point (f : X ⟶ Z) (g : Z ⟶ B) (T : Over S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ B` over `S`. -/
  a : ofOver T ⟶ B
  /-- The morphism `b : T ×_B Z ⟶ X` of functors of points. -/
  b : fiber a g ⟶ X.functorOfPoints
  /-- The morphism `b` lies over `Z`. -/
  w : b ≫ asFunctor f = fiberSnd a g

namespace Point

/-- Build a restriction-of-scalars pair from a morphism `a : T ⟶ B` and a morphism
`b : T ×_B Z ⟶ X` over `Z`. -/
def of {f : X ⟶ Z} {g : Z ⟶ B} {T : Over S} (a : ofOver T ⟶ B)
    (b : fiber a g ⟶ X.functorOfPoints)
    (w : b ≫ asFunctor f = fiberSnd a g) :
    Point f g T where
  a := a
  b := b
  w := w

/-- A restriction-of-scalars pair is a morphism `T ×_B Z ⟶ X` over `Z`. -/
theorem spec {f : X ⟶ Z} {g : Z ⟶ B} {T : Over S} (p : Point f g T) :
    p.b ≫ asFunctor f = fiberSnd p.a g :=
  p.w

/-- The functor-of-points element of `B` determined by the morphism `a`. -/
def a_elem {f : X ⟶ Z} {g : Z ⟶ B} {T : Over S} (p : Point f g T) :
    B.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ B.functorOfPoints)

/-- Base change of a restriction-of-scalars pair along `φ : T' ⟶ T` preserves the
over-`Z` triangle. -/
theorem restrict_w {f : X ⟶ Z} {g : Z ⟶ B} {T T' : Over S} (p : Point f g T)
    (φ : T' ⟶ T) :
    (fiberMap φ p.a g ≫ p.b) ≫ asFunctor f =
      fiberSnd (ofOverMap φ ≫ p.a) g :=
  sorry

/-- Base change of a pair `(a, b)` along `φ : T' ⟶ T`, sending `a` to `a ∘ φ` and
precomposing `b` with `T' ×_B Z ⟶ T ×_B Z`. -/
def restrict {f : X ⟶ Z} {g : Z ⟶ B} {T T' : Over S} (p : Point f g T)
    (φ : T' ⟶ T) : Point f g T' :=
  of (ofOverMap φ ≫ p.a) (fiberMap φ p.a g ≫ p.b) (restrict_w p φ)

end Point

/-- The restriction-of-scalars presheaf `Res_{Z/B}(X)` on schemes over `S`. -/
def functor (f : X ⟶ Z) (g : Z ⟶ B) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Point f g T.unop
  map {T T'} φ := TypeCat.ofHom fun (p : Point f g T.unop) ↦ p.restrict φ.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluating the restriction-of-scalars presheaf at `T` recovers the type of pairs
over `T`. -/
theorem functor_obj (f : X ⟶ Z) (g : Z ⟶ B) (T : Over S) :
    (functor f g).obj (op T) = Point f g T :=
  rfl

/-- The restriction-of-scalars presheaf is an fppf sheaf on `Over S`. -/
theorem isSheaf (f : X ⟶ Z) (g : Z ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor f g) :=
  sorry

/-- The restriction-of-scalars sheaf `Res_{Z/B}(X)` on `(Sch/S)_fppf`. -/
def sheaf (f : X ⟶ Z) (g : Z ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨functor f g, isSheaf f g⟩

/-- Evaluating `sheaf f g` on `T` recovers the type of restriction-of-scalars pairs
over `T`. -/
theorem sheaf_obj (f : X ⟶ Z) (g : Z ⟶ B) (T : Over S) :
    (sheaf f g).obj.obj (op T) = Point f g T :=
  rfl

/-- Forgetting the over-`Z` condition to an over-`B` relative-Hom pair. -/
theorem toRelativeHom_w (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Point f g T) :
    p.b ≫ asFunctor (f ≫ g) = fiberSnd p.a g ≫ asFunctor g :=
  (Category.assoc p.b (asFunctor f) (asFunctor g)).symm.trans
    (congrArg (fun k ↦ k ≫ asFunctor g) p.w)

/-- The relative-Hom pair associated to a restriction-of-scalars pair. -/
def toRelativeHomPoint (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Point f g T) :
    RelativeHom.Point g (f ≫ g) T :=
  RelativeHom.Point.of p.a p.b (toRelativeHom_w f g p)

/-- The forgetful map `Res_{Z/B}(X) ⟶ Mor_B(Z, X)` of fppf sheaves. -/
def toRelativeHom (f : X ⟶ Z) (g : Z ⟶ B) :
    sheaf f g ⟶ RelativeHom.sheaf g (f ≫ g) :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : Point f g T.unop) ↦ toRelativeHomPoint f g p
      naturality := sorry }

/-- Components of `toRelativeHom` are `toRelativeHomPoint`. -/
theorem toRelativeHom_app (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (toRelativeHom f g).hom.app T =
      TypeCat.ofHom fun (p : Point f g T.unop) ↦ toRelativeHomPoint f g p :=
  rfl

/-- The component of `Res_{Z/B}(X) ⟶ B` sending a pair `(a, b)` to the
universe-raised section `a`. -/
def toBaseApp (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ)
    (p : Point f g T.unop) : (uliftFunctorOfPoints B).obj T :=
  ULift.up p.a_elem

/-- The structure morphism `Res_{Z/B}(X) ⟶ B` of fppf sheaves. -/
def toBase (f : X ⟶ Z) (g : Z ⟶ B) : sheaf f g ⟶ uliftSheafOfPoints B :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (toBaseApp f g T)
      naturality := sorry }

/-- Components of `toBase` are `toBaseApp`. -/
theorem toBase_app (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (toBase f g).hom.app T = TypeCat.ofHom (toBaseApp f g T) :=
  rfl

/-- On a pair `(a, b)`, the structure morphism records `a` as the universe-raised
section `Point.a_elem`. -/
theorem toBase_spec (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Point f g T) :
    (toBase f g).hom.app (op T) p = ULift.up p.a_elem :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
