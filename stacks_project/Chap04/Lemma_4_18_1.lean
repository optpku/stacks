/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.FinitelyGenerated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vI uI vC uC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I] [Finite I]
variable (hgen : (⊤ : MorphismProperty I).IsFinitelyGenerated)

/- Lemma 4.18.1 (1): a finite-object category with finitely generated arrows admits one finite
comparison category whose functor is both initial and final and preserves nonemptiness. -/
@[stacks 05XU "finite initial-final reduction and nonemptiness comparison"]
#check (MorphismProperty.IsFinitelyGenerated.existsReduction hgen :
  Nonempty (FiniteInitialFinalReduction I))

variable {C : Type uC} [Category.{vC} C]
variable (R : FiniteInitialFinalReduction I) (M : I ⥤ C)

/- Lemma 4.18.1 (2): limit existence is invariant under an initial reduction functor. -/
@[stacks 05XU "limit existence under the finite initial reduction"]
#check (Functor.Initial.hasLimit_comp_iff R.functor :
  HasLimit (R.functor ⋙ M) ↔ HasLimit M)

section

variable [HasLimit M]

/- Lemma 4.18.1 (3): an initial reduction gives the canonical limit comparison. -/
@[stacks 05XU "canonical limit isomorphism under the finite initial reduction"]
#check (Functor.Initial.limitIso R.functor M :
  limit (R.functor ⋙ M) ≅ limit M)

end

/- Lemma 4.18.1 (4): colimit existence is invariant under a final reduction functor. -/
@[stacks 05XU "colimit existence under the finite final reduction"]
#check (Functor.Final.hasColimit_comp_iff R.functor :
  HasColimit (R.functor ⋙ M) ↔ HasColimit M)

section

variable [HasColimit M]

/- Lemma 4.18.1 (5): a final reduction gives the canonical colimit comparison. -/
@[stacks 05XU "canonical colimit isomorphism under the finite final reduction"]
#check (Functor.Final.colimitIso R.functor M :
  colimit (R.functor ⋙ M) ≅ colimit M)

end

/- Lemma 4.18.1 (6): connectedness is invariant under an initial reduction functor. -/
@[stacks 05XU "connectedness comparison for the finite initial reduction"]
#check (Functor.isConnected_iff_of_initial R.functor :
  IsConnected R.index ↔ IsConnected I)

end CategoryTheory
