module

public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Pasting.Comparison

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (sq : Bicategory.PseudoPullbackCone z (f ≫ g))

namespace Factorization

/- This namespace adds only the fibre comparison specific to iterated dotted-arrow pasting.
The category owner and its projection live in DottedArrow.Factorization, while optional
groupoid-fibration infrastructure lives in the corresponding InGroupoids leaf. -/

section FiberComparisonImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The total factorization object attached to a left-factor dotted arrow. -/
private def fiberTotalObj
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    Functor.MappingPath (factorRightFunctor sq) where
  fst := d
  snd := (pasteFunctor sq d).obj A
  iso := (factorPasteNatIso sq d).app A

/-- The total factorization object projects to d.

Proof strategy: unfold fiberTotalObj and projection; the equality is the first projection. -/
private theorem fiberTotalObj_projection
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    (projection sq).obj (fiberTotalObj sq d A) = d := sorry

/-- The factorization object packaged in the standard fibre over d. -/
private def fiberObj
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    (projection sq).Fiber d :=
  Functor.Fiber.mk (a := fiberTotalObj sq d A) (fiberTotalObj_projection sq d A)

/-- Compatibility of the two components of the total factorization morphism.

Proof strategy: simplify the identity first component and use the naturality of factorPasteNatIso
in the reverse direction. -/
private theorem fiberTotalMap_w
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    (𝟭 (DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))).map (𝟙 d) ≫
        (fiberTotalObj sq d A').iso.hom =
      (fiberTotalObj sq d A).iso.hom ≫
        (factorRightFunctor sq).map ((pasteFunctor sq d).map η) := sorry

/-- The morphism of total factorization objects attached to a left-factor morphism. -/
private def fiberTotalMap
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    fiberTotalObj sq d A ⟶ fiberTotalObj sq d A' where
  fst := 𝟙 d
  snd := (pasteFunctor sq d).map η
  w := fiberTotalMap_w sq d η

/-- The total factorization morphism lies over the identity of d.

Proof strategy: the projection remembers its fst field, which is 𝟙 d; apply the canonical
IsHomLift constructor with the stored object equalities. -/
private theorem fiberTotalMap_isHomLift
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    (projection sq).IsHomLift (𝟙 d) (fiberTotalMap sq d η) := sorry

/-- The morphism in the factorization fibre induced by a left-factor morphism. -/
private def fiberMap
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    fiberObj sq d A ⟶ fiberObj sq d A' :=
  ⟨fiberTotalMap sq d η, fiberTotalMap_isHomLift sq d η⟩

/-- The fibre map preserves identities.

Proof strategy: apply Functor.Fiber.hom_ext and CategoricalPullback.hom_ext, then use the public
pasteFunctor map computation on the second component. -/
private theorem fiberMap_id
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    fiberMap sq d (𝟙 A) = 𝟙 (fiberObj sq d A) := sorry

/-- The fibre map preserves composition.

Proof strategy: apply Functor.Fiber.hom_ext and CategoricalPullback.hom_ext, then use functoriality
of pasteFunctor on the second component. -/
private theorem fiberMap_comp
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' A'' : DottedArrow (leftFactorSquare sq d)}
    (η : A ⟶ A') (θ : A' ⟶ A'') :
    fiberMap sq d (η ≫ θ) = fiberMap sq d η ≫ fiberMap sq d θ := sorry

end Implementation

/-- The canonical comparison from left-factor dotted arrows to the corresponding factorization
fibre. -/
@[stacks 0H1B "(3) canonical fibre comparison"]
def fiberComparison
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    DottedArrow (leftFactorSquare sq d) ⥤ (projection sq).Fiber d where
  obj := Implementation.fiberObj sq d
  map := Implementation.fiberMap sq d
  map_id := Implementation.fiberMap_id sq d
  map_comp := Implementation.fiberMap_comp sq d

end FiberComparisonImplementation

/-- The first component of a factorization-fibre comparison object.

Proof strategy: pass through Functor.Fiber.fiberInclusion and unfold the private total object. -/
@[simp] theorem fiberComparison.obj.fst
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((Functor.Fiber.fiberInclusion :
        (projection sq).Fiber d ⥤ Functor.MappingPath (factorRightFunctor sq)).obj
      ((fiberComparison sq d).obj A)).fst = d := sorry

/-- The second component of a factorization-fibre comparison object.

Proof strategy: pass through Functor.Fiber.fiberInclusion and unfold the private total object. -/
@[simp] theorem fiberComparison.obj.snd
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((Functor.Fiber.fiberInclusion :
        (projection sq).Fiber d ⥤ Functor.MappingPath (factorRightFunctor sq)).obj
      ((fiberComparison sq d).obj A)).snd = (pasteFunctor sq d).obj A := sorry

/-- The comparison isomorphism of a factorization-fibre comparison object.

Proof strategy: pass through Functor.Fiber.fiberInclusion and unfold the private total object. -/
@[simp] theorem fiberComparison.obj.iso
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    (A : DottedArrow (leftFactorSquare sq d)) :
    ((Functor.Fiber.fiberInclusion :
        (projection sq).Fiber d ⥤ Functor.MappingPath (factorRightFunctor sq)).obj
      ((fiberComparison sq d).obj A)).iso = (factorPasteNatIso sq d).app A := sorry

/-- The first component of a factorization-fibre comparison map.

Proof strategy: pass through Functor.Fiber.fiberInclusion and unfold the private total map. -/
@[simp] theorem fiberComparison.map.fst
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    ((Functor.Fiber.fiberInclusion :
        (projection sq).Fiber d ⥤ Functor.MappingPath (factorRightFunctor sq)).map
      ((fiberComparison sq d).map η)).fst = 𝟙 d := sorry

/-- The second component of a factorization-fibre comparison map.

Proof strategy: pass through Functor.Fiber.fiberInclusion and unfold the private total map. -/
@[simp] theorem fiberComparison.map.snd
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq))
    {A A' : DottedArrow (leftFactorSquare sq d)} (η : A ⟶ A') :
    ((Functor.Fiber.fiberInclusion :
        (projection sq).Fiber d ⥤ Functor.MappingPath (factorRightFunctor sq)).map
      ((fiberComparison sq d).map η)).snd = (pasteFunctor sq d).map η := sorry

/-- The canonical left-factor comparison is an isomorphism of categories onto the fibre of the
factorization projection over the chosen middle dotted arrow.

This is the concrete comparison functor constructed above, rather than an anonymous existence
claim. In particular, typeclass search also obtains its induced categorical equivalence. -/
@[stacks 0H1B "(3) fibre comparison"]
instance fiberComparison.isIso
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (fiberComparison sq d).IsIso := sorry

end Factorization

end DottedArrow

end CategoryTheory
