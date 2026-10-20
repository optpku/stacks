/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Products.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Product

/-!
# Binary products of algebraic stacks

The 2-fibre product of algebraic stacks over a scheme `S` is the product of their
underlying groupoid fibrations over `(Sch/S)_fppf`. It remains an algebraic stack,
and is a product in the 2-category of algebraic stacks over `S`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y)))

/-- The ambient 1-morphism of `prodFst` is the first projection of the 2-fibre product. -/
theorem prodFst_hom {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    (prodFst X Y).hom = TwoFibreProduct.fst.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y)) :=
  sorry

/-- The second projection of a product of algebraic stacks. -/
def prodSnd {S : Scheme.{u}} (X Y : AlgebraicStacks S) : prod X Y ⟶ Y :=
  Bicategory.InducedBicategory.mkHom
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y)))

/-- The ambient 1-morphism of `prodSnd` is the second projection of the 2-fibre product. -/
theorem prodSnd_hom {S : Scheme.{u}} (X Y : AlgebraicStacks S) :
    (prodSnd X Y).hom = TwoFibreProduct.snd.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y)) :=
  sorry

/-- The test cone on the structure morphisms of `X` and `Y` with apex `T` presented by a
pair of 1-morphisms `f : T ⟶ X` and `g : T ⟶ Y`. -/
private def prodTestCone {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    PseudoPullbackCone
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y)) where
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
    (PseudoPullbackCone.lift (prodTestCone f g) (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))))

/-- Postcomposing `prodLift f g` with the first projection recovers `f` up to the
canonical invertible 2-morphism. -/
def prodLift_fst {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ prodFst X Y ≅ f :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.fstIso (prodTestCone f g) (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))))

/-- Postcomposing `prodLift f g` with the second projection recovers `g` up to the
canonical invertible 2-morphism. -/
def prodLift_snd {S : Scheme.{u}} {T X Y : AlgebraicStacks S} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ prodSnd X Y ≅ g :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.sndIso (prodTestCone f g) (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))))

/-- A pair of 2-morphisms acts componentwise on the test-cone transformations. -/
private def prodTestCone.map₂App {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {f f' : T ⟶ X} {g g' : T ⟶ Y} (η : f ⟶ f') (θ : g ⟶ g') :
    ∀ a : LocallyDiscrete WalkingCospan,
      (prodTestCone f g).toPseudoCone.π.app a ⟶
        (prodTestCone f' g').toPseudoCone.π.app a
  | ⟨none⟩ => η.hom ▷ baseProjection.{u + 1, u, u + 1} (toGroupoids X)
  | ⟨some WalkingPair.left⟩ => η.hom
  | ⟨some WalkingPair.right⟩ => θ.hom

/-- The componentwise action of a pair of 2-morphisms is natural on the walking cospan. -/
private theorem prodTestCone.map₂_naturality {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {f f' : T ⟶ X} {g g' : T ⟶ Y} (η : f ⟶ f') (θ : g ⟶ g')
    {a b : LocallyDiscrete WalkingCospan} (h : a ⟶ b) :
    (Pseudofunctor.const (LocallyDiscrete WalkingCospan) (toGroupoids T)).map h ◁
        prodTestCone.map₂App η θ b ≫ ((prodTestCone f' g').toPseudoCone.π.naturality h).hom =
      ((prodTestCone f g).toPseudoCone.π.naturality h).hom ≫
        prodTestCone.map₂App η θ a ▷
          (Bicategory.cospan
            (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
            (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).map h :=
  sorry

/-- The modification of test-cone transformations induced by a pair of 2-morphisms. -/
private def prodTestCone.map₂ {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {f f' : T ⟶ X} {g g' : T ⟶ Y} (η : f ⟶ f') (θ : g ⟶ g') :
    (prodTestCone f g).toPseudoCone.π ⟶ (prodTestCone f' g').toPseudoCone.π :=
  Pseudofunctor.StrongTrans.Hom.of
    { app := prodTestCone.map₂App η θ
      naturality := prodTestCone.map₂_naturality η θ }

/-- Whiskering by both product projections preserves identity 2-morphisms. -/
private theorem prodHomFunctor_map_id {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    (φ : T ⟶ prod X Y) :
    ((𝟙 φ) ▷ prodFst X Y, (𝟙 φ) ▷ prodSnd X Y) =
      (𝟙 (φ ≫ prodFst X Y), 𝟙 (φ ≫ prodSnd X Y)) := sorry

/-- Whiskering by both product projections preserves composition of 2-morphisms. -/
private theorem prodHomFunctor_map_comp {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    {φ ψ χ : T ⟶ prod X Y} (η : φ ⟶ ψ) (θ : ψ ⟶ χ) :
    ((η ≫ θ) ▷ prodFst X Y, (η ≫ θ) ▷ prodSnd X Y) =
      ((η ▷ prodFst X Y) ≫ (θ ▷ prodFst X Y),
        (η ▷ prodSnd X Y) ≫ (θ ▷ prodSnd X Y)) := sorry

/-- The hom-category functor sending a 1-morphism into `prod X Y` to its pair of
composites with the projections. -/
def prodHomFunctor {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ prod X Y) ⥤ (T ⟶ X) × (T ⟶ Y) where
  obj φ := (φ ≫ prodFst X Y, φ ≫ prodSnd X Y)
  map η := (η ▷ prodFst X Y, η ▷ prodSnd X Y)
  map_id := prodHomFunctor_map_id T X Y
  map_comp := prodHomFunctor_map_comp T X Y

/-- The universal lift sends a pair of 2-morphisms to a 2-morphism between pairings. -/
private def prodHomInverseMap {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    {p q : (T ⟶ X) × (T ⟶ Y)} (η : p ⟶ q) :
    prodLift p.1 p.2 ⟶ prodLift q.1 q.2 :=
  Bicategory.InducedBicategory.mkHom₂
    ((PseudoCone.lift.functor
      (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
        (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).toPseudoCone
      (toGroupoids T)).map (prodTestCone.map₂ η.1 η.2))

/-- Universal pairing preserves identity 2-morphisms. -/
private theorem prodHomInverse_map_id {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    (p : (T ⟶ X) × (T ⟶ Y)) :
    prodHomInverseMap (𝟙 p) = 𝟙 (prodLift p.1 p.2) := sorry

/-- Universal pairing preserves composition of pairs of 2-morphisms. -/
private theorem prodHomInverse_map_comp {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    {p q r : (T ⟶ X) × (T ⟶ Y)} (η : p ⟶ q) (θ : q ⟶ r) :
    prodHomInverseMap (η ≫ θ) = prodHomInverseMap η ≫ prodHomInverseMap θ := sorry

/-- The hom-category functor sending a pair of 1-morphisms to the induced pairing
into the product. -/
def prodHomInverse {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ X) × (T ⟶ Y) ⥤ (T ⟶ prod X Y) where
  obj p := prodLift p.1 p.2
  map η := prodHomInverseMap η
  map_id := prodHomInverse_map_id T X Y
  map_comp := prodHomInverse_map_comp T X Y

/-- The component isomorphisms identifying a cone with the test cone of its projections. -/
private def prodHomEquiv.unitComparisonApp {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    ∀ a : LocallyDiscrete WalkingCospan,
      (((TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
        (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).toPseudoCone.comparison
          (toGroupoids T)).obj φ.hom).app a ≅
        (prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y)).toPseudoCone.π.app a
  | ⟨none⟩ => (α_ φ.hom (prodFst X Y).hom (baseProjection.{u + 1, u, u + 1} (toGroupoids X))).symm
  | ⟨some WalkingPair.left⟩ => Iso.refl _
  | ⟨some WalkingPair.right⟩ => Iso.refl _

/-- The component isomorphisms of the cone comparison satisfy modification coherence. -/
private theorem prodHomEquiv.unitComparison_coherence {S : Scheme.{u}}
    {T X Y : AlgebraicStacks S} (φ : T ⟶ prod X Y)
    {a b : LocallyDiscrete WalkingCospan} (h : a ⟶ b) :
    (Pseudofunctor.const (LocallyDiscrete WalkingCospan) (toGroupoids T)).map h ◁
        (prodHomEquiv.unitComparisonApp φ b).hom ≫
          ((prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y)).toPseudoCone.π.naturality h).hom =
      (((((TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
        (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).toPseudoCone.comparison
          (toGroupoids T)).obj φ.hom).naturality h).hom) ≫
        (prodHomEquiv.unitComparisonApp φ a).hom ▷
          (Bicategory.cospan
            (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
            (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).map h :=
  sorry

/-- The comparison identifying the cone presented by a 1-morphism into the product
with the test cone of its projections. -/
private def prodHomEquiv.unitComparison {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    ((TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))).toPseudoCone.comparison (toGroupoids T)).obj φ.hom ≅
      (prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y)).toPseudoCone.π :=
  Pseudofunctor.StrongTrans.isoMk
    (prodHomEquiv.unitComparisonApp φ)
    (prodHomEquiv.unitComparison_coherence φ)

/-- The unit 2-isomorphism of the product hom-equivalence at a 1-morphism `φ`. -/
private def prodHomEquiv.unitApp {S : Scheme.{u}} {T X Y : AlgebraicStacks S}
    (φ : T ⟶ prod X Y) :
    φ ≅ prodLift (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y) :=
  Bicategory.InducedBicategory.isoMk
    (PseudoPullbackCone.lift.uniqueIso
      (prodTestCone (φ ≫ prodFst X Y) (φ ≫ prodSnd X Y))
      (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} (toGroupoids X))
      (baseProjection.{u + 1, u, u + 1} (toGroupoids Y))) φ.hom (prodHomEquiv.unitComparison φ))

/-- The unit isomorphisms of universal pairing are natural in maps into the product. -/
private theorem prodHomEquiv.unit_naturality {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    {φ ψ : T ⟶ prod X Y} (η : φ ⟶ ψ) :
    (𝟭 (T ⟶ prod X Y)).map η ≫ (prodHomEquiv.unitApp ψ).hom =
      (prodHomEquiv.unitApp φ).hom ≫
        (prodHomFunctor T X Y ⋙ prodHomInverse T X Y).map η := sorry

/-- The projection isomorphisms of universal pairing are natural in pairs of maps. -/
private theorem prodHomEquiv.counit_naturality {S : Scheme.{u}} (T X Y : AlgebraicStacks S)
    {p q : (T ⟶ X) × (T ⟶ Y)} (η : p ⟶ q) :
    (prodHomInverse T X Y ⋙ prodHomFunctor T X Y).map η ≫
        (Iso.prod (prodLift_fst q.1 q.2) (prodLift_snd q.1 q.2)).hom =
      (Iso.prod (prodLift_fst p.1 p.2) (prodLift_snd p.1 p.2)).hom ≫
        (𝟭 ((T ⟶ X) × (T ⟶ Y))).map η := sorry

/-- The product of algebraic stacks over `S` is a product in the 2-category
`AlgebraicStacks S`: maps into `prod X Y` are equivalent to pairs of maps. -/
def prodHomEquiv {S : Scheme.{u}} (T X Y : AlgebraicStacks S) :
    (T ⟶ prod X Y) ≌ (T ⟶ X) × (T ⟶ Y) :=
  CategoryTheory.Equivalence.mk
    (prodHomFunctor T X Y)
    (prodHomInverse T X Y)
    (NatIso.ofComponents (fun φ ↦ prodHomEquiv.unitApp φ)
      (prodHomEquiv.unit_naturality T X Y))
    (NatIso.ofComponents (fun p ↦ Iso.prod (prodLift_fst p.1 p.2) (prodLift_snd p.1 p.2))
      (prodHomEquiv.counit_naturality T X Y))

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
