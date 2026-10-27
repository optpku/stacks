/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Choice
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift.Comparison

/-!
# Choice independence for quasi-inverse lifts

This file records the canonical comparison between lifts formed with different quasi-inverses and
its coherence with their counit comparisons.
-/

@[expose] public section

universe vA uA vB uB vE uE

namespace CategoryTheory.Functor.QuasiInverse.liftFunctor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {E : Type uE} [Category.{vE} E]
variable {F : A ⥤ B}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem inverseIso_hom_counit_app (e e' : QuasiInverse F) (X : B) :
    F.map ((e.inverseIso e').hom.app X) ≫ e'.counitIso.hom.app X =
      e.counitIso.hom.app X := by
  have h : (e.inverseIso e').hom.app X =
      (Equivalence.adjointifyη e'.unitIso e'.counitIso).hom.app (e.inverse.obj X) ≫
        e'.inverse.map (e.counitIso.hom.app X) := by
    dsimp [inverseIso, Iso.isoInverseOfIsoFunctor, Iso.isoCompInverse,
      adjointifyUnit, Equivalence.mk]
    simp only [Category.id_comp, Category.comp_id]
  rw [h, F.map_comp, Category.assoc]
  have hε := e'.counitIso.hom.naturality (e.counitIso.hom.app X)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hε
  rw [hε, ← Category.assoc, Equivalence.adjointify_η_ε, Category.id_comp]

/-- The lift functors associated to two explicit quasi-inverses are naturally isomorphic on the
whole functor category. -/
def choiceNatIso (e e' : QuasiInverse F) (E : Type uE) [Category.{vE} E] :
    e.liftFunctor E ≅ e'.liftFunctor E :=
  (Functor.whiskeringRight E B A).mapIso (e.inverseIso e')

/-- Lifts of a fixed functor through two explicit quasi-inverses are naturally isomorphic. -/
def choiceIso (e e' : QuasiInverse F) (G : E ⥤ B) :
    (e.liftFunctor E).obj G ≅ (e'.liftFunctor E).obj G :=
  (choiceNatIso e e' E).app G

/-- Evaluating functor-level choice independence at `G` gives the pointwise choice
isomorphism. -/
@[simp]
theorem choiceNatIso.app (e e' : QuasiInverse F) (G : E ⥤ B) :
    (choiceNatIso e e' E).app G = choiceIso e e' G := rfl

/-- The forward component of lift choice-independence is the canonical comparison between the
two chosen inverse functors. -/
@[simp]
theorem choiceIso.hom.app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (choiceIso e e' G).hom.app X = (e.inverseIso e').hom.app (G.obj X) := rfl

/-- The inverse component of lift choice-independence is the inverse canonical comparison
between the two chosen inverse functors. -/
@[simp]
theorem choiceIso.inv.app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (choiceIso e e' G).inv.app X = (e.inverseIso e').inv.app (G.obj X) := rfl

/-- The forward choice comparison is natural in the functor being lifted. -/
@[reassoc]
theorem choiceIso.hom.naturality (e e' : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    e.inverse.map (β.app X) ≫ (choiceIso e e' H).hom.app X =
      (choiceIso e e' G).hom.app X ≫ e'.inverse.map (β.app X) :=
  (e.inverseIso e').hom.naturality (β.app X)

/-- The inverse choice comparison is natural in the functor being lifted. -/
@[reassoc]
theorem choiceIso.inv.naturality (e e' : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    e'.inverse.map (β.app X) ≫ (choiceIso e e' H).inv.app X =
      (choiceIso e e' G).inv.app X ≫ e.inverse.map (β.app X) :=
  (e.inverseIso e').inv.naturality (β.app X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Functor-level choice independence preserves the canonical lift comparison. -/
theorem choiceNatIso.comparison (e e' : QuasiInverse F) :
    Functor.isoWhiskerRight (choiceNatIso e e' E)
          ((Functor.whiskeringRight E A B).obj F) ≪≫
        comparisonNatIso e' E =
      comparisonNatIso e E := by
  ext G X
  dsimp [choiceNatIso, comparisonNatIso, liftFunctor, Equivalence.congrRight,
    Functor.isoWhiskerRight, Functor.whiskeringRight, adjointifyUnit, Equivalence.mk]
  simpa only [Category.id_comp, Category.comp_id] using
    inverseIso_hom_counit_app e e' (G.obj X)

/-- The canonical comparison between two quasi-inverse lifts respects their comparison with the
original functor. -/
theorem choiceIso.comparison (e e' : QuasiInverse F) (G : E ⥤ B) :
    Functor.isoWhiskerRight (choiceIso e e' G) F ≪≫ comparisonIso e' G =
      comparisonIso e G :=
  congrArg (fun α => α.app G) (choiceNatIso.comparison (E := E) e e')

/-- The forward component of quasi-inverse choice independence respects the supplied counits. -/
theorem choiceIso.hom.comparison_app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (Functor.isoWhiskerRight (choiceIso e e' G) F).hom.app X ≫
        (comparisonIso e' G).hom.app X =
      (comparisonIso e G).hom.app X :=
  NatTrans.congr_app (congrArg Iso.hom (choiceIso.comparison e e' G)) X

/-- The inverse component of quasi-inverse choice independence respects the supplied counits. -/
theorem choiceIso.inv.comparison_app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (comparisonIso e' G).inv.app X ≫
        (Functor.isoWhiskerRight (choiceIso e e' G) F).inv.app X =
      (comparisonIso e G).inv.app X :=
  NatTrans.congr_app (congrArg Iso.inv (choiceIso.comparison e e' G)) X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the chosen quasi-inverse preserves the lifted comparison. -/
theorem isoOfComparison.trans_choiceIso (e e' : QuasiInverse F)
    (L : E ⥤ A) (G : E ⥤ B) (α : L ⋙ F ≅ G) :
    isoOfComparison e L G α ≪≫ choiceIso e e' G =
      isoOfComparison e' L G α := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e'.counitIso.hom.app (G.obj X))).1
  have h (q : QuasiInverse F) :
      F.map ((isoOfComparison q L G α).hom.app X) ≫
          q.counitIso.hom.app (G.obj X) = α.hom.app X := by
    have hα : (isoOfComparison q L G α).hom.app X =
        (Equivalence.adjointifyη q.unitIso q.counitIso).hom.app (L.obj X) ≫
          q.inverse.map (α.hom.app X) := by
      dsimp [isoOfComparison, Iso.isoCompInverse, adjointifyUnit, Equivalence.mk,
        liftFunctor, Equivalence.congrRight, Functor.whiskeringRight]
      simp only [Category.id_comp]
    rw [hα, F.map_comp, Category.assoc]
    have hε := q.counitIso.hom.naturality (α.hom.app X)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hε
    rw [hε, ← Category.assoc, Equivalence.adjointify_η_ε, Category.id_comp]
  dsimp only [liftFunctor, Equivalence.congrRight, Functor.whiskeringRight,
    adjointifyUnit, Equivalence.mk]
  change F.map ((isoOfComparison e L G α).hom.app X ≫
      (e.inverseIso e').hom.app (G.obj X)) ≫ e'.counitIso.hom.app (G.obj X) =
    F.map ((isoOfComparison e' L G α).hom.app X) ≫ e'.counitIso.hom.app (G.obj X)
  rw [F.map_comp, Category.assoc, inverseIso_hom_counit_app, h, h]

/-- The choice comparison from a quasi-inverse to itself is the identity. -/
@[simp]
theorem choiceIso.refl (e : QuasiInverse F) (G : E ⥤ B) :
    choiceIso e e G = Iso.refl ((e.liftFunctor E).obj G) := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e).hom.app (G.obj X)) ≫ _ = F.map (𝟙 _) ≫ _
  rw [inverseIso_hom_counit_app, F.map_id, Category.id_comp]

/-- Reversing a choice comparison exchanges its two quasi-inverses. -/
@[simp]
theorem choiceIso.symm (e e' : QuasiInverse F) (G : E ⥤ B) :
    (choiceIso e e' G).symm = choiceIso e' e G := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e').inv.app (G.obj X)) ≫ _ =
    F.map ((e'.inverseIso e).hom.app (G.obj X)) ≫ _
  rw [inverseIso_hom_counit_app, ← inverseIso_hom_counit_app e e' (G.obj X),
    ← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, Category.id_comp]

/-- Choice comparisons compose transitively. -/
theorem choiceIso.trans (e e' e'' : QuasiInverse F) (G : E ⥤ B) :
    choiceIso e e' G ≪≫ choiceIso e' e'' G = choiceIso e e'' G := by
  ext X
  apply e.adjointifyUnit.fullyFaithfulFunctor.map_injective
  apply (cancel_mono (e''.counitIso.hom.app (G.obj X))).1
  change F.map ((e.inverseIso e').hom.app (G.obj X) ≫
      (e'.inverseIso e'').hom.app (G.obj X)) ≫ _ =
    F.map ((e.inverseIso e'').hom.app (G.obj X)) ≫ _
  rw [F.map_comp, Category.assoc, inverseIso_hom_counit_app,
    inverseIso_hom_counit_app, inverseIso_hom_counit_app]

/-- The choice comparison from a lift functor to itself is the identity natural isomorphism. -/
@[simp]
theorem choiceNatIso.refl (e : QuasiInverse F) :
    choiceNatIso e e E = Iso.refl (e.liftFunctor E) := by
  ext G X
  exact NatTrans.congr_app (congrArg Iso.hom (choiceIso.refl e G)) X

/-- Reversing a functor-level choice comparison exchanges its two quasi-inverses. -/
@[simp]
theorem choiceNatIso.symm (e e' : QuasiInverse F) :
    (choiceNatIso e e' E).symm = choiceNatIso e' e E := by
  ext G X
  exact NatTrans.congr_app (congrArg Iso.hom (choiceIso.symm e e' G)) X

/-- Functor-level choice comparisons compose transitively. -/
theorem choiceNatIso.trans (e e' e'' : QuasiInverse F) :
    choiceNatIso e e' E ≪≫ choiceNatIso e' e'' E =
      choiceNatIso e e'' E := by
  ext G X
  exact NatTrans.congr_app (congrArg Iso.hom (choiceIso.trans e e' e'' G)) X

/- Axiom audit: `choiceIso` is the whiskering of the explicit canonical inverse-functor
comparison; its computation and coherence proofs use the equivalence triangle identities. -/

end CategoryTheory.Functor.QuasiInverse.liftFunctor
