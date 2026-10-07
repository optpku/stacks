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

/-- The lift functors associated to two explicit quasi-inverses are naturally isomorphic on the
whole functor category. -/
@[stacks 04W9 "choice independence for functor-category quasi-inverse lifts"]
def choiceNatIso (e e' : QuasiInverse F) (E : Type uE) [Category.{vE} E] :
    e.liftFunctor E ≅ e'.liftFunctor E :=
  (Functor.whiskeringRight E B A).mapIso (e.inverseIso e')

/-- Lifts of a fixed functor through two explicit quasi-inverses are naturally isomorphic. -/
@[stacks 04W9 "pointwise choice independence for quasi-inverse lifts"]
def choiceIso (e e' : QuasiInverse F) (G : E ⥤ B) :
    (e.liftFunctor E).obj G ≅ (e'.liftFunctor E).obj G :=
  (choiceNatIso e e' E).app G

/-- Evaluating functor-level choice independence at `G` gives the pointwise choice
isomorphism. -/
@[simp]
theorem choiceNatIso.app (e e' : QuasiInverse F) (G : E ⥤ B) :
    (choiceNatIso e e' E).app G = choiceIso e e' G := sorry

/-- The forward component of lift choice-independence is the canonical comparison between the
two chosen inverse functors. -/
@[simp]
theorem choiceIso.hom.app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (choiceIso e e' G).hom.app X = (e.inverseIso e').hom.app (G.obj X) := sorry

/-- The inverse component of lift choice-independence is the inverse canonical comparison
between the two chosen inverse functors. -/
@[simp]
theorem choiceIso.inv.app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (choiceIso e e' G).inv.app X = (e.inverseIso e').inv.app (G.obj X) := sorry

/-- The forward choice comparison is natural in the functor being lifted. -/
@[reassoc]
theorem choiceIso.hom.naturality (e e' : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    e.inverse.map (β.app X) ≫ (choiceIso e e' H).hom.app X =
      (choiceIso e e' G).hom.app X ≫ e'.inverse.map (β.app X) := sorry

/-- The inverse choice comparison is natural in the functor being lifted. -/
@[reassoc]
theorem choiceIso.inv.naturality (e e' : QuasiInverse F) {G H : E ⥤ B}
    (β : G ⟶ H) (X : E) :
    e'.inverse.map (β.app X) ≫ (choiceIso e e' H).inv.app X =
      (choiceIso e e' G).inv.app X ≫ e.inverse.map (β.app X) := sorry

/-- Functor-level choice independence preserves the canonical lift comparison. -/
theorem choiceNatIso.comparison (e e' : QuasiInverse F) :
    Functor.isoWhiskerRight (choiceNatIso e e' E)
          ((Functor.whiskeringRight E A B).obj F) ≪≫
        comparisonNatIso e' E =
      comparisonNatIso e E := sorry

/-- The canonical comparison between two quasi-inverse lifts respects their comparison with the
original functor. -/
theorem choiceIso.comparison (e e' : QuasiInverse F) (G : E ⥤ B) :
    Functor.isoWhiskerRight (choiceIso e e' G) F ≪≫ comparisonIso e' G =
      comparisonIso e G := sorry

/-- The forward component of quasi-inverse choice independence respects the supplied counits. -/
theorem choiceIso.hom.comparison_app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (Functor.isoWhiskerRight (choiceIso e e' G) F).hom.app X ≫
        (comparisonIso e' G).hom.app X =
      (comparisonIso e G).hom.app X := sorry

/-- The inverse component of quasi-inverse choice independence respects the supplied counits. -/
theorem choiceIso.inv.comparison_app (e e' : QuasiInverse F) (G : E ⥤ B) (X : E) :
    (comparisonIso e' G).inv.app X ≫
        (Functor.isoWhiskerRight (choiceIso e e' G) F).inv.app X =
      (comparisonIso e G).inv.app X := sorry

/-- Changing the chosen quasi-inverse preserves the lifted comparison. -/
theorem isoOfComparison.trans_choiceIso (e e' : QuasiInverse F)
    (L : E ⥤ A) (G : E ⥤ B) (α : L ⋙ F ≅ G) :
    isoOfComparison e L G α ≪≫ choiceIso e e' G =
      isoOfComparison e' L G α := sorry

/-- The choice comparison from a quasi-inverse to itself is the identity. -/
@[simp]
theorem choiceIso.refl (e : QuasiInverse F) (G : E ⥤ B) :
    choiceIso e e G = Iso.refl ((e.liftFunctor E).obj G) := sorry

/-- Reversing a choice comparison exchanges its two quasi-inverses. -/
@[simp]
theorem choiceIso.symm (e e' : QuasiInverse F) (G : E ⥤ B) :
    (choiceIso e e' G).symm = choiceIso e' e G := sorry

/-- Choice comparisons compose transitively. -/
theorem choiceIso.trans (e e' e'' : QuasiInverse F) (G : E ⥤ B) :
    choiceIso e e' G ≪≫ choiceIso e' e'' G = choiceIso e e'' G := sorry

/-- The choice comparison from a lift functor to itself is the identity natural isomorphism. -/
@[simp]
theorem choiceNatIso.refl (e : QuasiInverse F) :
    choiceNatIso e e E = Iso.refl (e.liftFunctor E) := sorry

/-- Reversing a functor-level choice comparison exchanges its two quasi-inverses. -/
@[simp]
theorem choiceNatIso.symm (e e' : QuasiInverse F) :
    (choiceNatIso e e' E).symm = choiceNatIso e' e E := sorry

/-- Functor-level choice comparisons compose transitively. -/
theorem choiceNatIso.trans (e e' e'' : QuasiInverse F) :
    choiceNatIso e e' E ≪≫ choiceNatIso e' e'' E =
      choiceNatIso e e'' E := sorry

/- Axiom audit: `choiceIso` is the whiskering of the explicit canonical inverse-functor
comparison; `sorryAx` is confined to its theorem-valued coherence API. -/

end CategoryTheory.Functor.QuasiInverse.liftFunctor
