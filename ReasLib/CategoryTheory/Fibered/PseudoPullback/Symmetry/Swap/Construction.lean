/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# The swap functor for explicit pseudo-pullbacks

This leaf constructs the based functor which exchanges the two legs of an explicit
pseudo-pullback and inverts its stored comparison. Computation, projection, structural
comparison, and involutivity APIs live in focused downstream leaves.
-/

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace PseudoPullback

noncomputable section
namespace Implementation

/-- Swap the two entries and invert the stored comparison of a pseudo-pullback object. -/
private def swapObj (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (PseudoPullback G F).obj :=
  mk G F (baseObj P)
    { fst := (fiberObj P).snd
      snd := (fiberObj P).fst
      iso := (fiberObj P).iso.symm }

/-- Swapping the component maps of a pseudo-pullback morphism preserves the inverted comparison
square. -/
private theorem swapMapComm (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    CommSq
      (G.toFunctor.map (sndMap φ))
      (comparison (swapObj F G P))
      (comparison (swapObj F G Q))
      (F.toFunctor.map (fstMap φ)) := sorry
/- Proof strategy: unfold `swapObj`; take the inverse orientation of `comm F G φ`. The two
boundary maps are exchanged, so the inverse comparison square is exactly the required square. -/

/-- The first swapped component lifts the unchanged common base map. -/
private theorem swapMapFstIsHomLift (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    Y.p.IsHomLift (PseudoPullback.baseMap (F := F) (G := G) φ) (sndMap φ) := sorry
-- Proof strategy: reuse the lift property of the source second component.

/-- The second swapped component lifts the unchanged common base map. -/
private theorem swapMapSndIsHomLift (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    X.p.IsHomLift (PseudoPullback.baseMap (F := F) (G := G) φ) (fstMap φ) := sorry
-- Proof strategy: reuse the lift property of the source first component.

/-- Swap the component maps of a pseudo-pullback morphism. -/
private def swapMap (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) : swapObj F G P ⟶ swapObj F G Q :=
  PseudoPullback.Hom.mk (PseudoPullback.baseMap (F := F) (G := G) φ)
    (sndMap φ) (swapMapFstIsHomLift F G φ)
    (fstMap φ) (swapMapSndIsHomLift F G φ)
    (swapMapComm F G φ)

/-- The swap map preserves identities. -/
private theorem swapMapId
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    swapMap F G (𝟙 P) = 𝟙 (swapObj F G P) := sorry
/- Proof strategy: apply `hom_ext`; the exchanged first and second components are identity maps. -/

/-- The swap map preserves composition. -/
private theorem swapMapComp (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q R : (PseudoPullback F G).obj} (φ : P ⟶ Q) (χ : Q ⟶ R) :
    swapMap F G (φ ≫ χ) = swapMap F G φ ≫ swapMap F G χ := sorry
/- Proof strategy: apply `hom_ext`; both exchanged components preserve composition componentwise. -/

/-- The ordinary functor swapping the two sides of an explicit pseudo-pullback. -/
private def swapFunctor (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (PseudoPullback F G).obj ⥤ (PseudoPullback G F).obj where
  obj := swapObj F G
  map := swapMap F G
  map_id := swapMapId F G
  map_comp := swapMapComp F G

/-- The ordinary swap functor commutes strictly with the common base projection. -/
private theorem swapFunctorCompProjection (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swapFunctor F G ⋙ (PseudoPullback G F).p = (PseudoPullback F G).p := sorry
/- Proof strategy: use `Functor.ext`; swapping leaves `baseObj` and `baseMap` unchanged. -/

end Implementation

/-- The explicit based functor swapping the two sides of a pseudo-pullback. -/
@[stacks 0040 "swap map of an explicit pseudo-pullback"]
def swap (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    PseudoPullback F G ⥤ᵇ PseudoPullback G F where
  toFunctor := Implementation.swapFunctor F G
  w := Implementation.swapFunctorCompProjection F G

end

end PseudoPullback
end BasedCategory
end CategoryTheory
