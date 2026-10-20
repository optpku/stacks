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
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SpacesOver
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

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

/-- The product structural morphism is representable by algebraic spaces. -/
theorem tensor_representable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P Q : SpacesOver X) :
    relativelyRepresentableByAlgebraicSpaces
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
    (tensor_representable P Q)

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

/-- The objectwise comparison isomorphism of a pair of 1-morphisms of
`SpacesOver X` with common source, obtained from their structural comparison
cells. -/
def pairComparison {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    (toFunctor (map f ≫ hom P)).obj a ≅ (toFunctor (map g ≫ hom Q)).obj a :=
  (BasedNatIso.toNatIso ((Bicategory.InducedBicategory.forget.mapFunctor (left T) X).mapIso
      (facIso f ≪≫ (facIso g).symm))).app a

section PairingImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The pairing comparison is vertical over the common base object. -/
private theorem Implementation.pairComparison_isHomLift {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    X.p.IsHomLift (𝟙 ((left T).p.obj a)) (pairComparison f g a).hom := sorry

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
      iso := Functor.Fiber.isoMk (pairComparison f g a)
        (Implementation.pairComparison_isHomLift f g a) }

/-- The fst pairing component lies over the common base arrow. -/
private theorem Implementation.pairMap_fst_isHomLift {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    (left P).p.IsHomLift ((left T).p.map φ) ((toFunctor (map f)).map φ) := sorry

/-- The snd pairing component lies over the common base arrow. -/
private theorem Implementation.pairMap_snd_isHomLift {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    (left Q).p.IsHomLift ((left T).p.map φ) ((toFunctor (map g)).map φ) := sorry

/-- The pairing components respect the fibre-product comparison. -/
private theorem Implementation.pairMap_comm {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    CommSq
      ((toFunctor (hom P)).map ((toFunctor (map f)).map φ))
      (BasedCategory.PseudoPullback.comparison (pairObj f g a))
      (BasedCategory.PseudoPullback.comparison (pairObj f g b))
      ((toFunctor (hom Q)).map ((toFunctor (map g)).map φ)) := sorry

/-- The morphism of chosen 2-fibre products associated to a morphism in the
common source of a pair of 1-morphisms of `SpacesOver X`. -/
def pairMap {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    pairObj f g a ⟶ pairObj f g b :=
  BasedCategory.PseudoPullback.Hom.mk ((left T).p.map φ)
    ((toFunctor (map f)).map φ) (Implementation.pairMap_fst_isHomLift f g φ)
    ((toFunctor (map g)).map φ) (Implementation.pairMap_snd_isHomLift f g φ)
    (Implementation.pairMap_comm f g φ)

/-- Pairing preserves identity arrows. -/
private theorem Implementation.pairBasedFunctor_map_id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    pairMap f g (𝟙 a) = 𝟙 (pairObj f g a) := sorry

/-- Pairing preserves composition. -/
private theorem Implementation.pairBasedFunctor_map_comp {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b c : (left T).total} (φ : a ⟶ b) (ψ : b ⟶ c) :
    pairMap f g (φ ≫ ψ) = pairMap f g φ ≫ pairMap f g ψ := sorry

/-- Pairing preserves the projection to the base. -/
private theorem Implementation.pairBasedFunctor_comm {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    ({ obj := pairObj f g
       map := pairMap f g
       map_id := Implementation.pairBasedFunctor_map_id f g
       map_comp := Implementation.pairBasedFunctor_map_comp f g } :
      (left T).total ⥤ (tensorApex P Q).total) ⋙ (tensorApex P Q).p = (left T).p := sorry

/-- The based functor into the chosen 2-fibre product induced by a pair of
1-morphisms of `SpacesOver X` with common source. -/
def pairBasedFunctor {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    (left T).toBasedCategory ⥤ᵇ (tensorApex P Q).toBasedCategory where
  obj := pairObj f g
  map := pairMap f g
  map_id := Implementation.pairBasedFunctor_map_id f g
  map_comp := Implementation.pairBasedFunctor_map_comp f g
  w := Implementation.pairBasedFunctor_comm f g

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

/-- The first-projection comparison is natural. -/
private theorem Implementation.pairOver_fst_naturality {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q)
    {a b : (left T).total} (φ : a ⟶ b) :
    (toFunctor (pairOver f g ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q))).map φ ≫ (pairOver_fstApp f g b).hom =
      (pairOver_fstApp f g a).hom ≫ (toFunctor (map f)).map φ := sorry

/-- The first-projection comparison is vertical. -/
private theorem Implementation.pairOver_fst_isHomLift {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) (a : (left T).total) :
    (left P).p.IsHomLift (𝟙 ((left T).p.obj a)) (pairOver_fstApp f g a).hom := sorry

/-- The first projection of `pairOver f g` recovers `map f`. -/
def pairOver_fstIso {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T P Q : SpacesOver X} (f : T ⟶ P) (g : T ⟶ Q) :
    pairOver f g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (hom P) (hom Q) ≅
      map f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (pairOver_fstApp f g) (Implementation.pairOver_fst_naturality f g)
      (Implementation.pairOver_fst_isHomLift f g))

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

/-- The chosen representative gives the original homotopy-category morphism. -/
theorem homRep_mkHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {P Q : Bicategory.HomotopyCategory (SpacesOver X)} (f : P ⟶ Q) :
    (Bicategory.HomotopyCategory.mkHom (homRep f) : P ⟶ Q) = f :=
  Quotient.out_eq f

/-- Every arrow to the identity object is its structural arrow. -/
private theorem Implementation.toId_unique {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Bicategory.HomotopyCategory (SpacesOver X))
    (m : P ⟶ Bicategory.HomotopyCategory.mk (id X)) :
    m = Bicategory.HomotopyCategory.mkHom (toId P.as) := sorry

/-- The chosen terminal cone in the homotopy category of `SpacesOver X`. -/
def terminalCone {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    LimitCone (Functor.empty.{0} (Bicategory.HomotopyCategory (SpacesOver X))) where
  cone := asEmptyCone (Bicategory.HomotopyCategory.mk (id X))
  isLimit :=
    IsTerminal.ofUniqueHom
      (fun P ↦ Bicategory.HomotopyCategory.mkHom (toId P.as)) Implementation.toId_unique

/-- Pairing followed by the fst projection recovers the component. -/
private theorem Implementation.homotopyLift_fst {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {P Q T : Bicategory.HomotopyCategory (SpacesOver X)}
    (f : T ⟶ P) (g : T ⟶ Q) :
    Bicategory.HomotopyCategory.mkHom (lift (homRep f) (homRep g)) ≫
      Bicategory.HomotopyCategory.mkHom (tensorFst P.as Q.as) = f := sorry

/-- Pairing followed by the snd projection recovers the component. -/
private theorem Implementation.homotopyLift_snd {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {P Q T : Bicategory.HomotopyCategory (SpacesOver X)}
    (f : T ⟶ P) (g : T ⟶ Q) :
    Bicategory.HomotopyCategory.mkHom (lift (homRep f) (homRep g)) ≫
      Bicategory.HomotopyCategory.mkHom (tensorSnd P.as Q.as) = g := sorry

/-- A product arrow is determined by its two projections. -/
private theorem Implementation.homotopyLift_unique {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {P Q T : Bicategory.HomotopyCategory (SpacesOver X)}
    (f : T ⟶ P) (g : T ⟶ Q)
    (m : T ⟶ Bicategory.HomotopyCategory.mk (tensor P.as Q.as))
    (hf : m ≫ Bicategory.HomotopyCategory.mkHom (tensorFst P.as Q.as) = f)
    (hg : m ≫ Bicategory.HomotopyCategory.mkHom (tensorSnd P.as Q.as) = g) :
    m = Bicategory.HomotopyCategory.mkHom (lift (homRep f) (homRep g)) := sorry

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
        Implementation.homotopyLift_fst Implementation.homotopyLift_snd
        Implementation.homotopyLift_unique }

/-- The homotopy 1-category of morphisms of algebraic stacks representable by
algebraic spaces, with target `X`, is cartesian monoidal, with tensor product
given by chosen 2-fibre products over `X`. -/
instance instCartesianMonoidalCategory_homotopy
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    CartesianMonoidalCategory (Bicategory.HomotopyCategory (SpacesOver X)) :=
  .ofChosenFiniteProducts (terminalCone X) productCone

end PairingImplementation

end AlgebraicGeometry.SpacesOver
