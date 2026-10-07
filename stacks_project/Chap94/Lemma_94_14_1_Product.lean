module

public import Mathlib.CategoryTheory.Products.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.Definition_94_12_3_AlgebraicStacks
public import stacks_project.Chap94.Lemma_94_6_5_Product

/-!
# Binary products of algebraic stacks

The 2-fibre product of algebraic stacks over a scheme `S` is the product of their
underlying groupoid fibrations over `(Sch/S)_fppf`. It remains an algebraic stack,
and is a product in the 2-category of algebraic stacks over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory Limits
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicStack

/-- The 2-fibre product of algebraic stacks over `S`, as categories fibred in groupoids
over `(Sch/S)_fppf`, is again an algebraic stack. -/
instance prod {S : Scheme.{u}} (X Y : GroupoidsOver S) [AlgebraicStack X] [AlgebraicStack Y] :
    AlgebraicStack (FiberedCategoryOver.Groupoids.prod X Y) := sorry

end AlgebraicStack

namespace AlgebraicStacks

/-- The canonical projection of an algebraic stack to the identity fibration on `Over S`. -/
abbrev toBase {S : Scheme.{u}} (X : AlgebraicStacks S) :
    toGroupoids X ⟶ base.{u + 1, u, u + 1} (Over S) :=
  baseProjection.{u + 1, u, u + 1} (toGroupoids X)

/-- The product of algebraic stacks over `S` in the 2-category `AlgebraicStacks S`. -/
def prod {S : Scheme.{u}} (X Y : AlgebraicStacks S) : AlgebraicStacks S :=
  of (FiberedCategoryOver.Groupoids.prod (toGroupoids X) (toGroupoids Y))

/-- Packaging the product in `AlgebraicStacks` forgets to the 2-fibre product of the
underlying groupoid fibrations. -/
theorem prod_toGroupoids {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    toGroupoids (prod X Y) =
      FiberedCategoryOver.Groupoids.prod (toGroupoids X) (toGroupoids Y) := sorry

/-- The first projection of a product of algebraic stacks. -/
def prodFst {S : Scheme.{u}} (X Y : AlgebraicStacks S) : prod X Y ⟶ X :=
  Bicategory.InducedBicategory.mkHom
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (toBase X) (toBase Y))

/-- The ambient 1-morphism of `prodFst` is the first projection of the 2-fibre product. -/
theorem prodFst_hom {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    (prodFst X Y).hom = TwoFibreProduct.fst.{u + 1, u, u + 1, u} (toBase X) (toBase Y) :=
  sorry

/-- The second projection of a product of algebraic stacks. -/
def prodSnd {S : Scheme.{u}} (X Y : AlgebraicStacks S) : prod X Y ⟶ Y :=
  Bicategory.InducedBicategory.mkHom
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (toBase X) (toBase Y))

/-- The ambient 1-morphism of `prodSnd` is the second projection of the 2-fibre product. -/
theorem prodSnd_hom {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    (prodSnd X Y).hom = TwoFibreProduct.snd.{u + 1, u, u + 1, u} (toBase X) (toBase Y) :=
  sorry

/-- The canonical 2-fibre-product cone of the structure morphisms of `X` and `Y`. -/
abbrev prodCone {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    PseudoPullbackCone (toBase X) (toBase Y) :=
  TwoFibreProduct.cone.{u + 1, u, u + 1, u} (toBase X) (toBase Y)

/-- The test cone on the structure morphisms of `X` and `Y` with apex `T` presented by a
pair of 1-morphisms `f : T ⟶ X` and `g : T ⟶ Y`. -/
def prodTestCone {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    PseudoPullbackCone (toBase X) (toBase Y) where
  pt := toGroupoids T
  fst := f.hom
  snd := g.hom
  iso :=
    baseProjection.naturality.{u + 1, u} f.hom ≪≫
      (baseProjection.naturality.{u + 1, u} g.hom).symm

/-- The pairing 1-morphism `T ⟶ prod X Y` induced by `f : T ⟶ X` and `g : T ⟶ Y`. -/
def prodLift {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    T ⟶ prod X Y :=
  Bicategory.InducedBicategory.mkHom
    (PseudoPullbackCone.lift (prodTestCone f g) (prodCone X Y))

/-- Postcomposing `prodLift f g` with the first projection recovers `f` up to the
canonical invertible 2-morphism. -/
def prodLift_fst {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ prodFst X Y ≅ f :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.fstIso (prodTestCone f g) (prodCone X Y))

/-- Postcomposing `prodLift f g` with the second projection recovers `g` up to the
canonical invertible 2-morphism. -/
def prodLift_snd {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ prodSnd X Y ≅ g :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.sndIso (prodTestCone f g) (prodCone X Y))

/-- The modification of test-cone transformations induced by a pair of 2-morphisms. -/
def prodTestCone.map₂ {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {f f' : T ⟶ X} {g g' : T ⟶ Y} (η : f ⟶ f') (θ : g ⟶ g') :
    (prodTestCone f g).toPseudoCone.π ⟶ (prodTestCone f' g').toPseudoCone.π :=
  Pseudofunctor.StrongTrans.Hom.of
    { app := fun a ↦
        match a with
        | ⟨none⟩ => η.hom ▷ toBase X
        | ⟨some WalkingPair.left⟩ => η.hom
        | ⟨some WalkingPair.right⟩ => θ.hom
      naturality := sorry }

/-- The hom-category functor sending a 1-morphism into `prod X Y` to its pair of
composites with the projections. -/
def prodHomFunctor {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ prod X Y) ⥤ (T ⟶ X) × (T ⟶ Y) where
  obj φ := (φ ≫ prodFst X Y, φ ≫ prodSnd X Y)
  map η := (η ▷ prodFst X Y, η ▷ prodSnd X Y)
  map_id := sorry
  map_comp := sorry

/-- The hom-category functor sending a pair of 1-morphisms to the induced pairing
into `prod X Y`. -/
def prodHomInverse {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ X) × (T ⟶ Y) ⥤ (T ⟶ prod X Y) where
  obj p := prodLift p.1 p.2
  map η :=
    Bicategory.InducedBicategory.mkHom₂
      ((PseudoCone.lift.functor (prodCone X Y).toPseudoCone (toGroupoids T)).map
        (prodTestCone.map₂ η.1 η.2))
  map_id := sorry
  map_comp := sorry

/-- The comparison identifying the cone presented by a 1-morphism into the product
with the test cone of its projections. -/
def prodHomEquiv.unitComparison {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    ((prodCone X Y).toPseudoCone.comparison (toGroupoids T)).obj φ.hom ≅
      (prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y)).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk
    (fun a ↦
      match a with
      | ⟨none⟩ => (α_ φ.hom (prodFst X Y).hom (toBase X)).symm
      | ⟨some WalkingPair.left⟩ => Iso.refl _
      | ⟨some WalkingPair.right⟩ => Iso.refl _)
    sorry

/-- The unit 2-isomorphism of the product hom-equivalence at a 1-morphism `φ`. -/
def prodHomEquiv.unitApp {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    φ ≅ prodLift (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y) :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.uniqueIso
      (prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y))
      (prodCone X Y) φ.hom (prodHomEquiv.unitComparison φ))

/-- The product of algebraic stacks over `S` is a product in the 2-category
`AlgebraicStacks S`: maps into `prod X Y` are equivalent to pairs of maps. -/
def prodHomEquiv {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ prod X Y) ≌ (T ⟶ X) × (T ⟶ Y) :=
  CategoryTheory.Equivalence.mk
    (prodHomFunctor T X Y)
    (prodHomInverse T X Y)
    (NatIso.ofComponents (fun φ ↦ prodHomEquiv.unitApp φ) sorry)
    (NatIso.ofComponents (fun p ↦ Iso.prod (prodLift_fst p.1 p.2) (prodLift_snd p.1 p.2)) sorry)

/-- The forward functor of `prodHomEquiv` evaluates a 1-morphism as its pair of
composites with the projections. -/
theorem prodHomEquiv_apply {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    (prodHomEquiv T X Y).functor.obj φ = (φ ≫ prodFst X Y, φ ≫ prodSnd X Y) := sorry

/-- The inverse functor of `prodHomEquiv` evaluates a pair of 1-morphisms as the
induced pairing. -/
theorem prodHomEquiv_symm_apply {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (f : T ⟶ X) (g : T ⟶ Y) :
    (prodHomEquiv T X Y).inverse.obj (f, g) = prodLift f g := sorry

/-- A 1-morphism into `prod X Y` whose composites with the projections recover `f` and `g`
up to invertible 2-morphisms is 2-isomorphic to `prodLift f g`. -/
theorem prodLift_unique {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {f : T ⟶ X} {g : T ⟶ Y} (k : T ⟶ prod X Y)
    (hf : k ≫ prodFst X Y ≅ f) (hg : k ≫ prodSnd X Y ≅ g) :
    Nonempty (k ≅ prodLift f g) := sorry

end AlgebraicStacks

end AlgebraicGeometry
