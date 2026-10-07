module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Projection
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Postcomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Structural comparison for the pseudo-pullback swap

This leaf assembles the inverted objectwise comparison into a based natural isomorphism and
relates it to the original pseudo-pullback comparison through the two projection isomorphisms.
-/

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
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

/-- The swapped object already carries the required inverse structural comparison. -/
private def swapComparisonIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :=
  PseudoPullback.comparisonIsoApp (F := G) (G := F) ((swap F G).obj P)

end Implementation

/-- The objectwise structural comparison after swapping is the inverse of the original
comparison. This direct component owner works across independent total-category universes. -/
def swap.comparisonIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (((swap F G ⋙ PseudoPullback.fst G F) ⋙ G).obj P) ≅
      (((swap F G ⋙ PseudoPullback.snd G F) ⋙ F).obj P) :=
  Implementation.swapComparisonIsoApp F G P

/-- The objectwise inverse comparisons after swapping are natural in pseudo-pullback
morphisms. -/
theorem swap.comparisonIsoApp.naturality
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((swap F G ⋙ PseudoPullback.fst G F) ⋙ G).map φ ≫
        (swap.comparisonIsoApp F G Q).hom =
      (swap.comparisonIsoApp F G P).hom ≫
        ((swap F G ⋙ PseudoPullback.snd G F) ⋙ F).map φ := sorry

/-- Every swapped structural comparison is vertical over the identity common base map. -/
theorem swap.comparisonIsoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    S.p.IsHomLift (𝟙 ((PseudoPullback F G).p.obj P))
      (swap.comparisonIsoApp F G P).hom := sorry

/-- The structural comparison after swapping, assembled directly from the inverse objectwise
comparisons. This construction remains available across independent total-category universes. -/
@[stacks 0040 "structural comparison after the explicit pseudo-pullback swap"]
def swap.comparisonIso (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap F G ⋙ PseudoPullback.fst G F) ⋙ G ≅
      (swap F G ⋙ PseudoPullback.snd G F) ⋙ F :=
  BasedNatIso.ofComponents
    (swap.comparisonIsoApp F G)
    (fun φ ↦ swap.comparisonIsoApp.naturality F G φ)
    (swap.comparisonIsoApp.isHomLift F G)

/-- The forward component of the swapped structural comparison is the inverse of the original
comparison component. -/
@[simp]
theorem swap.comparisonIso.hom.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.comparisonIso F G).hom.toNatTrans.app P =
      (swap.comparisonIsoApp F G P).hom := sorry

/-- The inverse component of the swapped structural comparison is the original comparison
component. -/
@[simp]
theorem swap.comparisonIso.inv.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.comparisonIso F G).inv.toNatTrans.app P =
      (swap.comparisonIsoApp F G P).inv := sorry

/-- The swapped structural comparison is the inverse original comparison transported across
the two projection comparisons. -/
@[stacks 0040 "comparison formula for pseudo-pullback symmetry"]
theorem swap.comparisonIso.eq (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap.comparisonIso F G =
      (BasedCategory.postcomposition (PseudoPullback F G) G).mapIso
          (swap.fstIso F G) ≪≫
        (PseudoPullback.comparisonIso F G).symm ≪≫
          (BasedCategory.postcomposition (PseudoPullback F G) F).mapIso
            (swap.sndIso F G).symm := sorry

end

end PseudoPullback
end BasedCategory
end CategoryTheory
