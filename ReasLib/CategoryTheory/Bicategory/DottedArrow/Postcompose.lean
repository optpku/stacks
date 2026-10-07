module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Postcompose

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace DottedArrow

section Postcompose

variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable {S : Bicategory.PseudoPullbackCone y p}
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The upper-left comparison of a postcomposed dotted arrow. -/
private def postcomposeLeftIso (A : DottedArrow S) :
    S.fst ≫ (A.arrow ≫ q) ≅ S.snd ≫ q :=
  (α_ S.fst A.arrow q).symm ≪≫ whiskerRightIso A.left q

/-- The lower-right comparison of a postcomposed dotted arrow. -/
private def postcomposeRightIso (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    y ≫ g ≅ (A.arrow ≫ q) ≫ f :=
  whiskerRightIso A.right g ≪≫ α_ A.arrow p g ≪≫
    whiskerLeftIso A.arrow φ ≪≫ (α_ A.arrow q f).symm

/-- The two postcomposed triangular comparisons recover the outer-square comparison. -/
private theorem postcomposeComm (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    whiskerLeftIso S.fst (postcomposeRightIso φ A) ≪≫
        (α_ S.fst (A.arrow ≫ q) f).symm ≪≫
          whiskerRightIso (postcomposeLeftIso A) f =
      (S.postcompose φ).iso := sorry
/- Proof strategy: expand `postcomposeLeftIso`, `postcomposeRightIso`, and
`Bicategory.PseudoPullbackCone.postcompose`; rewrite the central part with `A.comm`, then use
associator naturality, `Bicategory.whisker_exchange_assoc`, and bicategorical coherence to match
the two explicit outer-rectangle composites. -/

/-- Postcomposing a dotted arrow with the right square gives a dotted arrow for the outer
rectangle. -/
private def postcompose (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    DottedArrow (S.postcompose φ) where
  arrow := A.arrow ≫ q
  left := postcomposeLeftIso A
  right := postcomposeRightIso φ A
  comm := postcomposeComm φ A

/-- Compatibility of the whiskered ambient `2`-morphism with the left postcomposed triangle.

Proof strategy: expand `postcomposeLeftIso`, use `η.left_comm`, and normalize with
associator naturality. -/
private theorem postcomposeMap_left_comm
    (φ : p ≫ g ≅ q ≫ f) {A A' : DottedArrow S} (η : A ⟶ A') :
    S.fst ◁ (η.hom ▷ q) ≫ (postcompose φ A').left.hom =
      (postcompose φ A).left.hom := sorry

/-- Compatibility of the whiskered ambient `2`-morphism with the right postcomposed triangle.

Proof strategy: expand `postcomposeRightIso`, use `η.right_comm`, and normalize with
associator naturality and `Bicategory.whisker_exchange_assoc`. -/
private theorem postcomposeMap_right_comm
    (φ : p ≫ g ≅ q ≫ f) {A A' : DottedArrow S} (η : A ⟶ A') :
    (postcompose φ A).right.hom ≫ (η.hom ▷ q) ▷ f =
      (postcompose φ A').right.hom := sorry

/-- The morphism of postcomposed dotted arrows induced by a source morphism. -/
private def postcomposeMap
    (φ : p ≫ g ≅ q ≫ f) {A A' : DottedArrow S} (η : A ⟶ A') :
    postcompose φ A ⟶ postcompose φ A' where
  hom := η.hom ▷ q
  left_comm := postcomposeMap_left_comm φ η
  right_comm := postcomposeMap_right_comm φ η

/-- Postcomposition preserves identity dotted-arrow morphisms.

Proof strategy: apply `DottedArrow.Hom.ext`; the ambient component is
`Bicategory.id_whiskerRight`. -/
private theorem postcomposeMap_id (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    postcomposeMap φ (𝟙 A) = 𝟙 (postcompose φ A) := sorry

/-- Postcomposition preserves composition of dotted-arrow morphisms.

Proof strategy: apply `DottedArrow.Hom.ext`; the ambient component is
`Bicategory.comp_whiskerRight`. -/
private theorem postcomposeMap_comp (φ : p ≫ g ≅ q ≫ f)
    {A₀ A₁ A₂ : DottedArrow S} (η : A₀ ⟶ A₁) (θ : A₁ ⟶ A₂) :
    postcomposeMap φ (η ≫ θ) = postcomposeMap φ η ≫ postcomposeMap φ θ := sorry

end Implementation

/-- The canonical functor on dotted-arrow categories induced by postcomposing with a right
square. -/
def postcomposeFunctor
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f) :
    DottedArrow S ⥤ DottedArrow (S.postcompose φ) where
  obj := Implementation.postcompose φ
  map := Implementation.postcomposeMap φ
  map_id := Implementation.postcomposeMap_id φ
  map_comp := Implementation.postcomposeMap_comp φ

end

/-- The object part of postcomposition composes the dotted arrow with the right leg.

Proof strategy: unfold `postcomposeFunctor` and its private object implementation. -/
@[simp]
theorem postcomposeFunctor.obj.arrow
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    ((postcomposeFunctor S φ).obj A).arrow = A.arrow ≫ q := sorry

/-- The left triangle of a postcomposed dotted arrow is the original left triangle whiskered
by the right-square leg. -/
@[simp]
theorem postcomposeFunctor.obj.left
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    ((postcomposeFunctor S φ).obj A).left =
      (α_ S.fst A.arrow q).symm ≪≫ whiskerRightIso A.left q := sorry

/-- The right triangle of a postcomposed dotted arrow is obtained by pasting its original right
triangle with the specified right square. -/
@[simp]
theorem postcomposeFunctor.obj.right
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f) (A : DottedArrow S) :
    ((postcomposeFunctor S φ).obj A).right =
      whiskerRightIso A.right g ≪≫ α_ A.arrow p g ≪≫
        whiskerLeftIso A.arrow φ ≪≫ (α_ A.arrow q f).symm := sorry

/-- The morphism part of postcomposition right-whiskers the underlying `2`-morphism.

Proof strategy: unfold `postcomposeFunctor` and its private morphism implementation. -/
@[simp]
theorem postcomposeFunctor.map.hom
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f)
    {A A' : DottedArrow S} (η : A ⟶ A') :
    ((postcomposeFunctor S φ).map η).hom = η.hom ▷ q := sorry

/-- The mapped ambient cell satisfies the left triangular compatibility after
postcomposition. -/
@[simp]
theorem postcomposeFunctor.map.leftComm
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f)
    {A A' : DottedArrow S} (η : A ⟶ A') :
    S.fst ◁ ((postcomposeFunctor S φ).map η).hom ≫
        ((postcomposeFunctor S φ).obj A').left.hom =
      ((postcomposeFunctor S φ).obj A).left.hom := sorry

/-- The mapped ambient cell satisfies the right triangular compatibility after
postcomposition. -/
@[simp]
theorem postcomposeFunctor.map.rightComm
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f)
    {A A' : DottedArrow S} (η : A ⟶ A') :
    ((postcomposeFunctor S φ).obj A).right.hom ≫
        ((postcomposeFunctor S φ).map η).hom ▷ f =
      ((postcomposeFunctor S φ).obj A').right.hom := sorry

/- The concrete postcomposition functor is preferable to a bare existential equivalence:
`Functor.IsEquivalence` is mathlib's canonical property and yields a bundled equivalence through
`Functor.asEquivalence`. No stronger ambient pullback assumption is introduced: local
groupoidality is exactly the source's `(2,1)` hypothesis, and finality is imposed only on the
specified right square. -/

/-- If the right square `⟨X', q, p, φ.symm⟩` is `2`-cartesian, then
postcomposition with it induces an equivalence of the two dotted-arrow categories. -/
@[stacks 0H1A]
instance postcomposeFunctor.isEquivalence
    (S : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsLocallyGroupoid B]
    [(⟨X', q, p, φ.symm⟩ : Bicategory.PseudoPullbackCone f g).IsBilimit] :
    (postcomposeFunctor S φ).IsEquivalence := sorry
/- Proof strategy: apply `Bicategory.isBiterminal_iff_existsUnique_hom₂` to the pith of the right square. For an
outer dotted arrow, its right triangle defines a square over `f, g`; the unique morphism to the
final square reconstructs a source dotted arrow, and local groupoidality makes both comparison
`2`-cells invertible. The same uniqueness descends morphisms and proves full faithfulness; the
reconstruction proves essential surjectivity, which `Functor.IsEquivalence.mk` packages into the
claimed instance. -/

end Postcompose

end DottedArrow

end CategoryTheory
