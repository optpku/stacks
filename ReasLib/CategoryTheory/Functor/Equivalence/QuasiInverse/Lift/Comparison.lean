/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift.Basic

/-!
# Comparison API for quasi-inverse lifts

The comparison is built from one adjointified equivalence so its unit and counit satisfy the
triangle identities required by the universal property.
-/

@[expose] public section

universe vA uA vB uB vE uE

namespace CategoryTheory.Functor.QuasiInverse.liftFunctor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {E : Type uE} [Category.{vE} E]
variable {F : A ⥤ B}

/-- The counit of postcomposition by an adjointified equivalence, expressed as a natural
isomorphism on the whole functor category. Its component at `G` is the canonical comparison for
the lift of `G`. -/
@[stacks 04W9 "comparison for a functor-category quasi-inverse lift"]
def comparisonNatIso (e : QuasiInverse F) (E : Type uE) [Category.{vE} E] :
    e.liftFunctor E ⋙
        (Functor.whiskeringRight E A B).obj F ≅
      𝟭 (E ⥤ B) :=
  (e.adjointifyUnit.congrRight (E := E)).counitIso

/-- A comparison after applying the forward functor identifies a functor with the corresponding
lift through an explicit quasi-inverse. The quasi-inverse unit is adjointified so that this
comparison is coherent with the supplied counit. -/
@[stacks 04W9 "uniqueness of a functor-category quasi-inverse lift"]
def isoOfComparison (e : QuasiInverse F) (L : E ⥤ A) (G : E ⥤ B)
    (α : L ⋙ F ≅ G) :
    L ≅ (e.liftFunctor E).obj G :=
  Iso.isoCompInverse (H := e.adjointifyUnit) α

/-- The forward component of the canonical lift comparison is the adjointified unit followed by
the chosen inverse applied to the comparison component. -/
@[simp]
theorem isoOfComparison.hom.app (e : QuasiInverse F) (L : E ⥤ A) (G : E ⥤ B)
    (α : L ⋙ F ≅ G) (X : E) :
    (isoOfComparison e L G α).hom.app X =
      e.adjointifyUnit.unitIso.hom.app (L.obj X) ≫
        e.inverse.map (α.hom.app X) := sorry

/-- The inverse component of the canonical lift comparison applies the chosen inverse to the
inverse comparison component and then uses the adjointified unit backwards. -/
@[simp]
theorem isoOfComparison.inv.app (e : QuasiInverse F) (L : E ⥤ A) (G : E ⥤ B)
    (α : L ⋙ F ≅ G) (X : E) :
    (isoOfComparison e L G α).inv.app X =
      e.inverse.map (α.inv.app X) ≫
        e.adjointifyUnit.unitIso.inv.app (L.obj X) := sorry

/-- Applying the original functor after a quasi-inverse lift recovers the input functor through
the supplied counit. -/
@[stacks 04W9 "pointwise comparison for a functor-category quasi-inverse lift"]
def comparisonIso (e : QuasiInverse F) (G : E ⥤ B) :
    (e.liftFunctor E).obj G ⋙ F ≅ G :=
  (comparisonNatIso e E).app G

/-- Evaluating the functor-level lift comparison at `G` gives the pointwise comparison
isomorphism. -/
@[simp]
theorem comparisonNatIso.app (e : QuasiInverse F) (G : E ⥤ B) :
    (comparisonNatIso e E).app G = comparisonIso e G := sorry

/-- The forward component of the quasi-inverse lift comparison is the supplied counit
component. -/
@[simp]
theorem comparisonIso.hom.app (e : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (comparisonIso e G).hom.app X = e.counitIso.hom.app (G.obj X) := sorry

/-- The inverse component of the quasi-inverse lift comparison is the inverse counit
component. -/
@[simp]
theorem comparisonIso.inv.app (e : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (comparisonIso e G).inv.app X = e.counitIso.inv.app (G.obj X) := sorry

/-- The forward lift comparison is natural in the functor being lifted. -/
@[reassoc]
theorem comparisonIso.hom.naturality (e : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    F.map (e.inverse.map (β.app X)) ≫ (comparisonIso e H).hom.app X =
      (comparisonIso e G).hom.app X ≫ β.app X := sorry

/-- The inverse lift comparison is natural in the functor being lifted. -/
@[reassoc]
theorem comparisonIso.inv.naturality (e : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    β.app X ≫ (comparisonIso e H).inv.app X =
      (comparisonIso e G).inv.app X ≫ F.map (e.inverse.map (β.app X)) := sorry

/-- The canonical lift isomorphism recovers its supplied comparison after applying the original
functor. This is the triangle-coherent universal property of `isoOfComparison`. -/
theorem isoOfComparison.comparison (e : QuasiInverse F) (L : E ⥤ A) (G : E ⥤ B)
    (α : L ⋙ F ≅ G) :
    Functor.isoWhiskerRight (isoOfComparison e L G α) F ≪≫
        comparisonIso e G =
      α := sorry

/-- The forward component of the lift comparison triangle commutes objectwise. -/
theorem isoOfComparison.hom.comparison_app (e : QuasiInverse F)
    (L : E ⥤ A) (G : E ⥤ B) (α : L ⋙ F ≅ G) (X : E) :
    (Functor.isoWhiskerRight (isoOfComparison e L G α) F).hom.app X ≫
        (comparisonIso e G).hom.app X =
      α.hom.app X := sorry

/-- The inverse component of the lift comparison triangle commutes objectwise. -/
theorem isoOfComparison.inv.comparison_app (e : QuasiInverse F)
    (L : E ⥤ A) (G : E ⥤ B) (α : L ⋙ F ≅ G) (X : E) :
    (comparisonIso e G).inv.app X ≫
        (Functor.isoWhiskerRight (isoOfComparison e L G α) F).inv.app X =
      α.inv.app X := sorry

/-- The universal comparison characterizes the canonical lift isomorphism. -/
theorem isoOfComparison.eq_iff (e : QuasiInverse F) (L : E ⥤ A) (G : E ⥤ B)
    (α : L ⋙ F ≅ G) (β : L ≅ (e.liftFunctor E).obj G) :
    β = isoOfComparison e L G α ↔
      Functor.isoWhiskerRight β F ≪≫ comparisonIso e G = α := sorry

/-- Lifting the canonical comparison gives the identity isomorphism. -/
@[simp]
theorem isoOfComparison.self (e : QuasiInverse F) (G : E ⥤ B) :
    isoOfComparison e ((e.liftFunctor E).obj G) G (comparisonIso e G) =
      Iso.refl ((e.liftFunctor E).obj G) := sorry

/-- Postcomposing the supplied comparison before lifting agrees with postcomposing the resulting
lift isomorphism by the chosen inverse. -/
theorem isoOfComparison.trans (e : QuasiInverse F) (L : E ⥤ A)
    {G H : E ⥤ B} (α : L ⋙ F ≅ G) (β : G ≅ H) :
    isoOfComparison e L H (α ≪≫ β) =
      isoOfComparison e L G α ≪≫ Functor.isoWhiskerRight β e.inverse := sorry

/- Axiom audit: both isomorphisms are constructed by mathlib from `adjointifyUnit`; their
non-Prop data do not depend on `sorryAx`. -/

end CategoryTheory.Functor.QuasiInverse.liftFunctor
