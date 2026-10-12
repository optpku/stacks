/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_21_6_GroupoidInFunctors
public import stacks_project.Chap90.Remark_90_21_6_Representable

/-!
# Representable groupoids in functors, terminology

The shorthand “let `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)` be a groupoid
in functors on `C`” means a representable groupoid in functors.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory.GroupoidInFunctors

/-- Remark 90.21.6: we say “let `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)` be a
groupoid in functors on `C`” to mean that we have a representable groupoid in functors.
Thus `U` and `R` are objects of `C`, there are morphisms `s, t : U ⟶ R`, the pushout of
`s` and `t` exists, there is a morphism `c : R ⟶ pushout s t`, and the coyoneda quintuple
is a groupoid in functors on `C`. -/
@[stacks 06K8]
theorem Representable.spec {C : Type u} [Category.{v} C] (G : Representable C) :
    HasPushout G.s G.t ∧
      IsGroupoidInFunctors (coyoneda.obj (op G.U)) (coyoneda.obj (op G.R))
        (coyoneda.map G.s.op) (coyoneda.map G.t.op)
        (Representable.compApp G.s G.t G.c) :=
  sorry

end CategoryTheory.GroupoidInFunctors
