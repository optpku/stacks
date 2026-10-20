/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Yoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (S : ShortComplex A)

/- Lemma 12.5.8 (1) [05AA]: additive representable functors detect an exact short complex with
epimorphic final map. -/
@[stacks 05AA]
#check (S.exact_and_epi_iff_yoneda :
  (S.Exact ∧ Epi S.g) ↔
    ∀ N : A,
      (S.op.map (preadditiveYoneda.obj N)).Exact ∧
        Mono (S.op.map (preadditiveYoneda.obj N)).f)

/- Lemma 12.5.8 (2) [05AA]: additive corepresentable functors detect an exact short complex with
monomorphic initial map. -/
#check (S.exact_and_mono_iff_coyoneda :
  (S.Exact ∧ Mono S.f) ↔
    ∀ N : A,
      (S.map (preadditiveCoyoneda.obj (Opposite.op N))).Exact ∧
        Mono (S.map (preadditiveCoyoneda.obj (Opposite.op N))).f)

end
