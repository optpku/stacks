/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
import Mathlib.Tactic.CrossRefAttribute

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

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

namespace PseudoPullback

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The ordinary functor underlying the first projection from the explicit pseudo-pullback. -/
private def fstFunctor : (PseudoPullback F G).obj ⥤ X.obj where
  obj := fstObj
  map := fstMap
  map_id := fstMap.id
  map_comp := fstMap.comp

/-- The ordinary first projection commutes strictly with the common base projection. -/
private theorem fstFunctor_comp_projection :
    fstFunctor F G ⋙ X.p = (PseudoPullback F G).p := sorry

/-- The ordinary functor underlying the second projection from the explicit pseudo-pullback. -/
private def sndFunctor : (PseudoPullback F G).obj ⥤ Y.obj where
  obj := sndObj
  map := sndMap
  map_id := sndMap.id
  map_comp := sndMap.comp

/-- The ordinary second projection commutes strictly with the common base projection. -/
private theorem sndFunctor_comp_projection :
    sndFunctor F G ⋙ Y.p = (PseudoPullback F G).p := sorry

end Implementation

/-- The first projection from the explicit pseudo-pullback in `Cat/C`. -/
@[stacks 0040 "first projection from an explicit pseudo-pullback"]
def fst : PseudoPullback F G ⥤ᵇ X where
  toFunctor := Implementation.fstFunctor F G
  w := Implementation.fstFunctor_comp_projection F G

/-- The first projection sends a pseudo-pullback object to its stored first component. -/
@[simp]
theorem fst.obj (P : (PseudoPullback F G).obj) :
    (fst F G).obj P = fstObj P := sorry

/-- The first projection sends a pseudo-pullback morphism to its stored first component. -/
@[simp]
theorem fst.map {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (fst F G).map φ = fstMap φ := sorry

/-- The second projection from the explicit pseudo-pullback in `Cat/C`. -/
@[stacks 0040 "second projection from an explicit pseudo-pullback"]
def snd : PseudoPullback F G ⥤ᵇ Y where
  toFunctor := Implementation.sndFunctor F G
  w := Implementation.sndFunctor_comp_projection F G

/-- The second projection sends a pseudo-pullback object to its stored second component. -/
@[simp]
theorem snd.obj (P : (PseudoPullback F G).obj) :
    (snd F G).obj P = sndObj P := sorry

/-- The second projection sends a pseudo-pullback morphism to its stored second component. -/
@[simp]
theorem snd.map {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (snd F G).map φ = sndMap φ := sorry

/-- The forward component of the canonical base-comparison isomorphism for the first projection
is the stored first-component base identification. -/
@[simp]
theorem fst.projectionIso.hom.app (P : (PseudoPullback F G).obj) :
    (BasedFunctor.projectionIso (fst F G)).hom.app P =
      (fstBaseIso P).hom := sorry

/-- The inverse component of the canonical base-comparison isomorphism for the first projection
is the inverse stored first-component base identification. -/
@[simp]
theorem fst.projectionIso.inv.app (P : (PseudoPullback F G).obj) :
    (BasedFunctor.projectionIso (fst F G)).inv.app P =
      (fstBaseIso P).inv := sorry

/-- The forward component of the canonical base-comparison isomorphism for the second projection
is the stored second-component base identification. -/
@[simp]
theorem snd.projectionIso.hom.app (P : (PseudoPullback F G).obj) :
    (BasedFunctor.projectionIso (snd F G)).hom.app P =
      (sndBaseIso P).hom := sorry

/-- The inverse component of the canonical base-comparison isomorphism for the second projection
is the inverse stored second-component base identification. -/
@[simp]
theorem snd.projectionIso.inv.app (P : (PseudoPullback F G).obj) :
    (BasedFunctor.projectionIso (snd F G)).inv.app P =
      (sndBaseIso P).inv := sorry

noncomputable section

/-- The forward objectwise comparison maps are natural in pseudo-pullback morphisms. -/
@[reassoc]
theorem comparisonIsoApp.naturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    F.toFunctor.map ((fst F G).map φ) ≫ (comparisonIsoApp Q).hom =
      (comparisonIsoApp P).hom ≫ G.toFunctor.map ((snd F G).map φ) := sorry

/-- The inverse objectwise comparison maps are natural in pseudo-pullback morphisms.

This is the inverse orientation of `comparisonIsoApp.naturality`; exposing it directly avoids
manual cancellation of the stored comparison isomorphism in constructions that transport from
the second component to the first. -/
@[reassoc]
theorem comparisonIsoApp.invNaturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (comparisonIsoApp P).inv ≫ F.toFunctor.map ((fst F G).map φ) =
      G.toFunctor.map ((snd F G).map φ) ≫ (comparisonIsoApp Q).inv := sorry

/-- The canonical invertible comparison `fst F G ⋙ F ≅ snd F G ⋙ G` over `C`. -/
@[stacks 0040 "comparison isomorphism of an explicit pseudo-pullback"]
def comparisonIso : fst F G ⋙ F ≅ snd F G ⋙ G :=
  BasedNatIso.ofComponents
    (comparisonIsoApp)
    (fun φ ↦ comparisonIsoApp.naturality F G φ)
    (fun P ↦ comparison.isHomLift P)

/-- The forward component of the based comparison is the objectwise comparison isomorphism. -/
@[simp]
theorem comparisonIso.hom.app (P : (PseudoPullback F G).obj) :
    (comparisonIso F G).hom.toNatTrans.app P =
      (comparisonIsoApp P).hom := sorry

/-- The inverse component of the based comparison is the inverse objectwise comparison
isomorphism. -/
@[simp]
theorem comparisonIso.inv.app (P : (PseudoPullback F G).obj) :
    (comparisonIso F G).inv.toNatTrans.app P =
      (comparisonIsoApp P).inv := sorry

/-- The ordinary categorical square underlying the based pseudo-pullback. -/
@[stacks 0040 "categorical square underlying an explicit pseudo-pullback"]
def square : CategoricalPullback.CatCommSqOver F.toFunctor G.toFunctor
    (PseudoPullback F G).obj where
  fst := (fst F G).toFunctor
  snd := (snd F G).toFunctor
  iso := BasedNatIso.toNatIso (comparisonIso F G)

/-- The first leg of the underlying categorical square is the first pseudo-pullback
projection. -/
@[simp]
theorem square.fst :
    (square F G).fst = (fst F G).toFunctor := sorry

/-- The second leg of the underlying categorical square is the second pseudo-pullback
projection. -/
@[simp]
theorem square.snd :
    (square F G).snd = (snd F G).toFunctor := sorry

/-- The comparison of the underlying categorical square is the ordinary natural isomorphism
underlying the based comparison. -/
@[simp]
theorem square.iso :
    (square F G).iso =
      BasedNatIso.toNatIso (comparisonIso F G) := sorry

/-- The forward component of the underlying categorical square is the stored objectwise
pseudo-pullback comparison. -/
@[simp]
theorem square.iso.hom.app (P : (PseudoPullback F G).obj) :
    (square F G).iso.hom.app P = (comparisonIsoApp P).hom := sorry

/-- The inverse component of the underlying categorical square is the inverse stored objectwise
pseudo-pullback comparison. -/
@[simp]
theorem square.iso.inv.app (P : (PseudoPullback F G).obj) :
    (square F G).iso.inv.app P = (comparisonIsoApp P).inv := sorry

end

end PseudoPullback
end BasedCategory
end CategoryTheory
