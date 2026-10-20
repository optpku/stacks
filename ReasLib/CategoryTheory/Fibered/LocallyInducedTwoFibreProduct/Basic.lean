/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections

/-!
# Basic explicit two-fibre products in locally induced bicategories

This module owns the explicit apex, its two selected projections, the comparison isomorphism,
and the canonical pseudo-pullback cone.  Detection and all functorial constructions live in
separate layers.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS uT vT

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable {X Y S : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C) (fun X : P.FullSubbicategory ↦ X.1) Q}

/-- The explicit two-fibre-product apex in a locally induced bicategory. Its carrier and
projection are exactly the underlying based pseudo-pullback. Relative closure consumes the two
stored hom-property witnesses; the resulting object-property field is proof only. -/
@[stacks 02XQ "locally induced two-fibre-product apex"]
def apex (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q :=
  ⟨BasedCategory.PseudoPullback F.obj G.obj,
    BasedCategory.PseudoPullback.HomProperty.IsClosedUnder.pseudoPullback_mem
      F.obj G.obj F.property G.property⟩

/-- Forgetting the selected-object witness from the explicit apex recovers the underlying based
pseudo-pullback. -/
@[simp]
theorem apex.obj (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).1 = BasedCategory.PseudoPullback F.obj G.obj := sorry

/- Data audit: `#print axioms CategoryTheory.LocallyInduced.TwoFibreProduct.apex` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Inspection of the constructor above
confines `sorryAx` to the Prop-valued relative-closure witness; the based pseudo-pullback carrier
and all of its structure are the explicit existing owner. -/

/-! The selected hom property contains the two projections of every explicit based
pseudo-pullback formed from selected cospan legs. -/
namespace Projections

/-- The selected hom property contains the two projections of every explicit
two-fibre-product formed from selected cospan legs. -/
@[stacks 02XQ "selected two-fibre-product projections"]
class Has : Prop where
  /-- The first explicit pseudo-pullback projection satisfies the selected hom property. -/
  fst_mem {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) X (BasedCategory.PseudoPullback.fst F.obj G.obj)
  /-- The second explicit pseudo-pullback projection satisfies the selected hom property. -/
  snd_mem {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) Y (BasedCategory.PseudoPullback.snd F.obj G.obj)

/-- The selected hom property is detected by composition with the two explicit
two-fibre-product projections. -/
@[stacks 02XQ "projection detection for selected two-fibre-products"]
class IsDetected : Prop where
  /-- A map into an explicit pseudo-pullback is selected when both projection composites are
  selected. -/
  mem {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S)
    {T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (K : T.1 ⟶ (apex F G).1) :
    Q T X (K ≫ BasedCategory.PseudoPullback.fst F.obj G.obj) →
    Q T Y (K ≫ BasedCategory.PseudoPullback.snd F.obj G.obj) →
      Q T (apex F G) K

end Projections

variable [Projections.Has (P := P) (Q := Q)]

/-- The first projection from the explicit locally induced two-fibre product. -/
@[stacks 02XQ "left projection of the locally induced two-fibre product"]
def fst (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ X :=
  Bicategory.LocallyInducedBicategory.mkHom
    (BasedCategory.PseudoPullback.fst F.obj G.obj)
    (Projections.Has.fst_mem F G)

/-- Forgetting the selected first projection recovers the explicit based pseudo-pullback
projection. -/
@[simp]
theorem fst.obj (F : X ⟶ S) (G : Y ⟶ S) :
    (fst F G).obj = BasedCategory.PseudoPullback.fst F.obj G.obj := sorry

/-- The second projection from the explicit locally induced two-fibre product. -/
@[stacks 02XQ "right projection of the locally induced two-fibre product"]
def snd (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ Y :=
  Bicategory.LocallyInducedBicategory.mkHom
    (BasedCategory.PseudoPullback.snd F.obj G.obj)
    (Projections.Has.snd_mem F G)

/-- Forgetting the selected second projection recovers the explicit based pseudo-pullback
projection. -/
@[simp]
theorem snd.obj (F : X ⟶ S) (G : Y ⟶ S) :
    (snd F G).obj = BasedCategory.PseudoPullback.snd F.obj G.obj := sorry

namespace Projections

/-- The first selected projection is available as a hom-property witness in its bundled form. -/
lemma fst_mem (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) X (fst F G).obj := sorry

/-- The second selected projection is available as a hom-property witness in its bundled form. -/
lemma snd_mem (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) Y (snd F G).obj := sorry

variable [Projections.IsDetected (P := P) (Q := Q)]

/-- A map into a selected two-fibre product is selected when both projection composites are. -/
lemma mem_of_comp_fst_snd
    {T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S) (K : T.1 ⟶ (apex F G).1)
    (hfst : Q T X (K ≫ (fst F G).obj))
    (hsnd : Q T Y (K ≫ (snd F G).obj)) :
    Q T (apex F G) K := sorry

/-- Membership in the selected hom category of a two-fibre product is equivalent to membership
of both composites with its selected projections. -/
lemma mem_iff
    {T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S) (K : T.1 ⟶ (apex F G).1) :
    Q T (apex F G) K ↔
      Q T X (K ≫ (fst F G).obj) ∧ Q T Y (K ≫ (snd F G).obj) := sorry

end Projections

/-- The canonical invertible comparison between the two composites to the cospan base. -/
@[stacks 02XQ "comparison isomorphism of the locally induced two-fibre product"]
noncomputable def comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  (Q _ _).isoMk (BasedCategory.PseudoPullback.comparisonIso F.obj G.obj)

/-- Forgetting the forward selected comparison cell recovers the explicit based
pseudo-pullback comparison. -/
@[simp]
theorem comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).hom.hom =
      (BasedCategory.PseudoPullback.comparisonIso F.obj G.obj).hom := sorry

/-- Forgetting the inverse selected comparison cell recovers the inverse explicit based
pseudo-pullback comparison. -/
@[simp]
theorem comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).inv.hom =
      (BasedCategory.PseudoPullback.comparisonIso F.obj G.obj).inv := sorry

/-- The canonical pseudo-pullback cone in the locally induced bicategory. -/
@[stacks 02XQ "locally induced two-fibre-product cone"]
noncomputable def cone (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G where
  pt := apex F G
  fst := fst F G
  snd := snd F G
  iso := comparisonIso F G

/-- The apex of the canonical locally induced pseudo-pullback cone is the explicit
two-fibre-product owner. -/
@[simp]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the canonical locally induced pseudo-pullback cone is its first
projection. -/
@[simp]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the canonical locally induced pseudo-pullback cone is its second
projection. -/
@[simp]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the canonical locally induced pseudo-pullback cone is the explicit
comparison isomorphism. -/
@[simp]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

/-- The canonical locally induced cone after forgetting the selected-object and selected-morphism
witnesses. This is the reusable ordinary bicategorical cone underlying `cone F G`. -/
@[stacks 02XQ "forgotten locally induced two-fibre-product cone"]
noncomputable def cone.forget (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F.obj G.obj :=
  Bicategory.PseudoPullbackCone.forgetLocallyInduced (cone F G)

/-- The apex of the forgotten canonical locally induced cone is the explicit based
pseudo-pullback. -/
@[simp]
theorem cone.forget.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone.forget F G).pt =
      BasedCategory.PseudoPullback F.obj G.obj := sorry

/-- The first leg of the forgotten canonical locally induced cone is the explicit based
pseudo-pullback first projection. -/
@[simp]
theorem cone.forget.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone.forget F G).fst =
      BasedCategory.PseudoPullback.fst F.obj G.obj := sorry

/-- The second leg of the forgotten canonical locally induced cone is the explicit based
pseudo-pullback second projection. -/
@[simp]
theorem cone.forget.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone.forget F G).snd =
      BasedCategory.PseudoPullback.snd F.obj G.obj := sorry

/-- The comparison of the forgotten canonical locally induced cone is the explicit based
pseudo-pullback comparison. -/
@[simp]
theorem cone.forget.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone.forget F G).iso =
      BasedCategory.PseudoPullback.comparisonIso F.obj G.obj := sorry

end TwoFibreProduct
end LocallyInduced
end CategoryTheory
