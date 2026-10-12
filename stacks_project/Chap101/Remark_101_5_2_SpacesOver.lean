/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Category
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap100.Remark_100_3_7_SpacesOver
public import stacks_project.Chap101.Lemma_101_5_1

/-!
# Algebraic spaces over an algebraic stack, as a cartesian homotopy category

The 1-category of morphisms of algebraic stacks representable by algebraic
spaces, obtained as the homotopy category of `SpacesOver`, carries finite
products given by identity morphisms and chosen 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.SpacesOver

/-- The domain 1-morphism underlying a 1-morphism of `SpacesOver`. -/
def map {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    {P Q : SpacesOver Y} (f : P ⟶ Q) : left P ⟶ left Q :=
  Bicategory.PseudoCostructuredArrow.map f.hom

/-- The comparison isomorphism `map f ≫ hom Q ≅ hom P` of a 1-morphism of
`SpacesOver`. -/
def facIso {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    {P Q : SpacesOver Y} (f : P ⟶ Q) :
    map f ≫ hom Q ≅ hom P :=
  Bicategory.PseudoCostructuredArrow.facIso f.hom

/-- The identity morphism of an algebraic stack, as an object of `SpacesOver`. -/
def id {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : SpacesOver X :=
  mk (𝟙 X) (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable (𝟙 X))

/-- The domain of `id X` is `X`. -/
theorem id_left {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    left (id X) = X :=
  sorry

/-- The structural morphism of `id X` is the identity of `X`. -/
theorem id_hom {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    hom (id X) = 𝟙 X :=
  sorry

/-- The 2-fibre product of two objects of `SpacesOver X` is an algebraic stack. -/
instance instAlgebraicStack_apex {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P Q : SpacesOver X) :
    AlgebraicStack
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} (hom P) (hom Q)) :=
  sorry

/-- The chosen projection `fst ≫ hom P` of a 2-fibre product of objects of
`SpacesOver X` is locally of finite type, hence representable by algebraic
spaces. -/
instance instLocallyOfFiniteType_tensorHom {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P Q : SpacesOver X) :
    Groupoids.Hom.LocallyOfFiniteType
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≫ hom P) :=
  sorry

/-- The chosen 2-fibre product of two objects of `SpacesOver X`, as a groupoid
fibration over `S`. -/
abbrev tensorApex {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (hom P) (hom Q)

/-- The chosen binary product of objects of `SpacesOver X`, given by the 2-fibre
product of their structural morphisms. -/
def tensor {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) : SpacesOver X :=
  mk (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≫ hom P)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `tensor P Q` is the chosen 2-fibre product of `hom P` and
`hom Q`. -/
theorem tensor_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) :
    left (tensor P Q) =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (hom P) (hom Q) :=
  sorry

/-- The structural morphism of `tensor P Q` is the composite of the first
2-fibre-product projection with `hom P`. -/
theorem tensor_hom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) :
    hom (tensor P Q) =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≫ hom P :=
  sorry

/-- An object of `SpacesOver X` obtained as a binary tensor has algebraic-stack
domain and a structural morphism representable by algebraic spaces. -/
theorem tensor_spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) :
    AlgebraicStack (left (tensor P Q)) ∧
      relativelyRepresentableByAlgebraicSpaces (hom (tensor P Q)) :=
  sorry

/-- The first projection of the chosen binary product in `SpacesOver X`. -/
def tensorFst {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) : tensor P Q ⟶ P :=
  homMk (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q)) (Iso.refl _)

/-- The second projection of the chosen binary product in `SpacesOver X`. -/
def tensorSnd {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : SpacesOver X) : tensor P Q ⟶ Q :=
  homMk (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (hom P) (hom Q))
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (hom P) (hom Q))

/-- The unique 1-morphism from an object of `SpacesOver X` to the identity
object, given by its structural morphism. -/
def toId {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : SpacesOver X) : P ⟶ id X :=
  homMk (hom P) (ρ_ (hom P)).symm

/-- The based-functor isomorphism underlying a 2-isomorphism of morphisms of
categories fibred in groupoids. -/
def basedIso {S : Scheme.{u}} {X Y : GroupoidsOver S} {F G : X ⟶ Y} (e : F ≅ G) :
    F.hom ≅ G.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The objectwise comparison isomorphism of a pair of 1-morphisms of
`SpacesOver X` with common source, obtained from their structural comparison
cells. -/
def pairComparison {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    (toFunctor (map f ≫ hom P)).obj a ≅ (toFunctor (map g ≫ hom Q)).obj a :=
  (BasedNatIso.toNatIso (basedIso (facIso f ≪≫ (facIso g).symm))).app a

/-- The object of the chosen 2-fibre product associated to a pair of 1-morphisms
of `SpacesOver X` with common source. -/
def pairObj {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    (tensorApex P Q).total :=
  BasedCategory.PseudoPullback.mk
    (toBasedFunctor (hom P)) (toBasedFunctor (hom Q))
    ((left T).p.obj a)
    { fst := Functor.Fiber.mk ((toBasedFunctor (map f)).w_obj a)
      snd := Functor.Fiber.mk ((toBasedFunctor (map g)).w_obj a)
      iso := Functor.Fiber.isoMk (pairComparison f g a) sorry }

/-- The morphism of chosen 2-fibre products associated to a morphism in the
common source of a pair of 1-morphisms of `SpacesOver X`. -/
def pairMap {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    pairObj f g a ⟶ pairObj f g b :=
  BasedCategory.PseudoPullback.Hom.mk ((left T).p.map φ)
    ((toFunctor (map f)).map φ) sorry
    ((toFunctor (map g)).map φ) sorry
    sorry

/-- The based functor into the chosen 2-fibre product induced by a pair of
1-morphisms of `SpacesOver X` with common source. -/
def pairBasedFunctor {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    (left T).toBasedCategory ⥤ᵇ (tensorApex P Q).toBasedCategory where
  obj := pairObj f g
  map := pairMap f g
  map_id := sorry
  map_comp := sorry
  w := sorry

/-- The morphism of algebraic stacks into the chosen 2-fibre product induced by a
pair of 1-morphisms of `SpacesOver X` with common source. -/
def pairOver {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    left T ⟶ tensorApex P Q :=
  ofBasedFunctor (pairBasedFunctor f g)

/-- The object component of `pairOver f g ≫ fst` is the image under `map f`. -/
def pairOver_fstApp {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    (toFunctor
        (pairOver f g ≫
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q))).obj a ≅
      (toFunctor (map f)).obj a :=
  Iso.refl ((toFunctor (map f)).obj a)

/-- The first projection of `pairOver f g` recovers `map f`. -/
def pairOver_fstIso {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    pairOver f g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≅
      map f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (pairOver_fstApp f g) (fun _ ↦ sorry) (fun _ ↦ sorry))

/-- The structural comparison identifying `hom T` with the composite of
`pairOver f g` and the structural morphism of `tensor P Q`. -/
def pair_tensorIso {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    hom T ≅
      pairOver f g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≫ hom P :=
  (facIso f).symm ≪≫
    Bicategory.whiskerRightIso (pairOver_fstIso f g).symm (hom P) ≪≫
      (α_ (pairOver f g)
          (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q))
          (hom P)).symm

/-- The pairing of a pair of 1-morphisms of `SpacesOver X` with common source,
as a 1-morphism into the chosen binary product. -/
def lift {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) : T ⟶ tensor P Q :=
  homMk (pairOver f g) (pair_tensorIso f g)

/-- A chosen representative of a morphism in the homotopy category of
`SpacesOver X`. -/
def homRep {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {P Q : Bicategory.HomotopyCategory (SpacesOver X)}
    (f : P ⟶ Q) : P.as ⟶ Q.as :=
  Quotient.out f

/-- The chosen terminal cone in the homotopy category of `SpacesOver X`. -/
def terminalCone {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    LimitCone (Functor.empty.{0} (Bicategory.HomotopyCategory (SpacesOver X))) where
  cone := asEmptyCone (Bicategory.HomotopyCategory.mk (id X))
  isLimit :=
    IsTerminal.ofUniqueHom
      (fun P ↦ Bicategory.HomotopyCategory.mkHom (toId P.as)) sorry

/-- The chosen binary product cone in the homotopy category of `SpacesOver X`. -/
def productCone {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P Q : Bicategory.HomotopyCategory (SpacesOver X)) :
    LimitCone (Limits.pair P Q) :=
  let fan :=
    BinaryFan.mk
      (Bicategory.HomotopyCategory.mkHom (tensorFst P.as Q.as))
      (Bicategory.HomotopyCategory.mkHom (tensorSnd P.as Q.as))
  { cone := fan
    isLimit :=
      BinaryFan.IsLimit.mk fan
        (fun f g ↦ Bicategory.HomotopyCategory.mkHom (lift (homRep f) (homRep g)))
        (fun _ _ ↦ sorry) (fun _ _ ↦ sorry)
        (fun _ _ _ _ _ ↦ sorry) }

/-- The homotopy 1-category of morphisms of algebraic stacks representable by
algebraic spaces, with target `X`, is cartesian monoidal, with tensor product
given by chosen 2-fibre products over `X`. -/
instance instCartesianMonoidalCategory_homotopy
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    CartesianMonoidalCategory (Bicategory.HomotopyCategory (SpacesOver X)) :=
  .ofChosenFiniteProducts (terminalCone X) productCone

end AlgebraicGeometry.SpacesOver

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver

/-- The relative inertia morphism `I_{X/Y} ⟶ X`, as an object of `SpacesOver X`. -/
def asSpacesOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : SpacesOver X :=
  SpacesOver.mk (forget.{u + 1, u, u, u + 1} f)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `asSpacesOver f` is the relative inertia stack of `f`. -/
theorem asSpacesOver_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    SpacesOver.left (asSpacesOver f) = relativeInertia f :=
  sorry

/-- The structural morphism of `asSpacesOver f` is the relative-inertia forgetful
morphism. -/
theorem asSpacesOver_hom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    SpacesOver.hom (asSpacesOver f) = forget.{u + 1, u, u, u + 1} f :=
  sorry

/-- Packaged relative inertia has algebraic-stack domain, and its structure map
to `X` is representable by algebraic spaces. -/
theorem asSpacesOver_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    AlgebraicStack (SpacesOver.left (asSpacesOver f)) ∧
      relativelyRepresentableByAlgebraicSpaces (SpacesOver.hom (asSpacesOver f)) :=
  sorry

/-- Relative inertia as an object of the homotopy 1-category of algebraic-space
representable morphisms to `X`. -/
def asHomotopy {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Bicategory.HomotopyCategory (SpacesOver X) :=
  Bicategory.HomotopyCategory.mk (asSpacesOver f)

/-- The underlying `SpacesOver` object of `asHomotopy f` is `asSpacesOver f`. -/
theorem asHomotopy_as {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (asHomotopy f).as = asSpacesOver f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
