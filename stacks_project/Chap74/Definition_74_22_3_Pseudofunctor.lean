module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange

/-!
# Algebraic-space slices as a pseudofunctor

Pullback along a morphism of algebraic spaces over a scheme `S` gives the
contravariant pseudofunctor whose fibre over `X` is the slice category `Over X`.
Transition functors are `overPullback`, not the sorry-tainted `Over.pullback`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The cone identity witnessing that `𝟙 X.left` and `X.hom` form a cone over `X.hom` and
`𝟙 W`. -/
theorem overPullbackId_w {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    𝟙 X.left ≫ X.hom = X.hom ≫ 𝟙 W := sorry

/-- The underlying forward map of identity slice pullback, as the first projection. -/
def overPullbackIdHom {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    ((overPullback (𝟙 W)).obj X).left ⟶ X.left :=
  overPullbackFst (𝟙 W) X

/-- `overPullbackIdHom` is the first projection of slice pullback along an identity. -/
theorem overPullbackIdHom_eq {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    overPullbackIdHom X = overPullbackFst (𝟙 W) X := sorry

/-- The underlying inverse map of identity slice pullback, induced by the identity cone. -/
def overPullbackIdInv {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    X.left ⟶ ((overPullback (𝟙 W)).obj X).left :=
  pullbackLift X.hom (𝟙 W) (𝟙 X.left) X.hom (overPullbackId_w X)

/-- `overPullbackIdInv` is the mediating map of the identity cone. -/
theorem overPullbackIdInv_eq {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    overPullbackIdInv X =
      pullbackLift X.hom (𝟙 W) (𝟙 X.left) X.hom (overPullbackId_w X) := sorry

/-- Slice pullback along an identity morphism is naturally the identity functor. -/
noncomputable def overPullbackIdIso {S : Scheme.{u}} (W : AlgebraicSpace S) :
    overPullback (𝟙 W) ≅ 𝟭 (Over W) :=
  NatIso.ofComponents
    (fun X ↦
      Over.isoMk
        { hom := overPullbackIdHom X
          inv := overPullbackIdInv X
          hom_inv_id := sorry
          inv_hom_id := sorry }
        sorry)
    sorry

/-- The component of `overPullbackIdIso` is identity slice pullback on objects. -/
theorem overPullbackIdIso_hom_app {S : Scheme.{u}} {W : AlgebraicSpace S} (X : Over W) :
    ((overPullbackIdIso W).hom.app X).left = overPullbackIdHom X := sorry

/-- The first factor of the composite-pullback comparison, into the intermediate slice. -/
def overPullbackCompMid {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶ ((overPullback f).obj X).left :=
  pullbackLift X.hom f (overPullbackFst (g ≫ f) X)
    (overPullbackSnd (g ≫ f) X ≫ g) sorry

/-- `overPullbackCompMid` recovers the first projection of the composite pullback. -/
theorem overPullbackCompMid_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompMid f g X ≫ overPullbackFst f X =
      overPullbackFst (g ≫ f) X := sorry

/-- Underlying forward map of iterated slice pullback comparison. -/
def overPullbackCompHom {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback (g ≫ f)).obj X).left ⟶
      ((overPullback g).obj ((overPullback f).obj X)).left :=
  pullbackLift ((overPullback f).obj X).hom g (overPullbackCompMid f g X)
    (overPullbackSnd (g ≫ f) X) sorry

/-- `overPullbackCompHom` recovers the second projection of the composite pullback. -/
theorem overPullbackCompHom_snd {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompHom f g X ≫ overPullbackSnd g ((overPullback f).obj X) =
      overPullbackSnd (g ≫ f) X := sorry

/-- Underlying inverse map of iterated slice pullback comparison. -/
def overPullbackCompInv {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullback g).obj ((overPullback f).obj X)).left ⟶
      ((overPullback (g ≫ f)).obj X).left :=
  pullbackLift X.hom (g ≫ f)
    (overPullbackFst g ((overPullback f).obj X) ≫ overPullbackFst f X)
    (overPullbackSnd g ((overPullback f).obj X)) sorry

/-- `overPullbackCompInv` recovers the first projection of the iterated pullback. -/
theorem overPullbackCompInv_fst {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    overPullbackCompInv f g X ≫ overPullbackFst (g ≫ f) X =
      overPullbackFst g ((overPullback f).obj X) ≫ overPullbackFst f X := sorry

/-- Slice pullback along a composite is the composite of slice pullbacks. -/
noncomputable def overPullbackCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') :
    overPullback (g ≫ f) ≅ overPullback f ⋙ overPullback g :=
  NatIso.ofComponents
    (fun X ↦
      Over.isoMk
        { hom := overPullbackCompHom f g X
          inv := overPullbackCompInv f g X
          hom_inv_id := sorry
          inv_hom_id := sorry }
        sorry)
    sorry

/-- The component of `overPullbackCompIso` is the iterated fibre-product comparison. -/
theorem overPullbackCompIso_hom_app {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (X : Over B) :
    ((overPullbackCompIso f g).hom.app X).left = overPullbackCompHom f g X := sorry

/-- The associativity coherence for repeated slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_associator
    {S : Scheme.{u}} {X₀ X₁ X₂ X₃ : (AlgebraicSpace S)ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (overPullbackCompIso (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (overPullbackCompIso f.unop g.unop)).hom ▷
          (overPullback h.unop).toCatHom ≫
      (α_ (overPullback f.unop).toCatHom (overPullback g.unop).toCatHom
        (overPullback h.unop).toCatHom).hom ≫
      (overPullback f.unop).toCatHom ◁
        (Cat.Hom.isoMk (overPullbackCompIso g.unop h.unop)).inv ≫
      (Cat.Hom.isoMk (overPullbackCompIso f.unop (g ≫ h).unop)).inv =
        eqToHom rfl := sorry

/-- The left-unit coherence for slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_leftUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (overPullbackCompIso (𝟙 X).unop f.unop)).hom ≫
        (Cat.Hom.isoMk (overPullbackIdIso X.unop)).hom ▷
          (overPullback f.unop).toCatHom ≫
      (λ_ (overPullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The right-unit coherence for slice pullback of algebraic spaces. -/
theorem overPseudofunctor_map₂_rightUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (overPullbackCompIso f.unop (𝟙 Y).unop)).hom ≫
        (overPullback f.unop).toCatHom ◁
          (Cat.Hom.isoMk (overPullbackIdIso Y.unop)).hom ≫
      (ρ_ (overPullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The contravariant pseudofunctor of algebraic-space slices over `S`, with transition
functors given by `overPullback`. -/
noncomputable def overPseudofunctor (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Over X.unop))
    (fun f ↦ (overPullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (overPullbackIdIso X.unop))
    (fun f g ↦ Cat.Hom.isoMk (overPullbackCompIso f.unop g.unop))
    overPseudofunctor_map₂_associator
    overPseudofunctor_map₂_leftUnitor
    overPseudofunctor_map₂_rightUnitor

/-- The fibre of `overPseudofunctor` at `X` is the category of algebraic spaces over `X`. -/
theorem overPseudofunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (overPseudofunctor S).obj (.mk (.op X)) = Cat.of (Over X) := sorry

/-- The action of `overPseudofunctor` on a morphism of algebraic spaces is slice pullback. -/
theorem overPseudofunctor_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((overPseudofunctor S).map f.op.toLoc).toFunctor = overPullback f := sorry

end AlgebraicGeometry.AlgebraicSpace
