module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Representable
import StacksCheckRecall

/-!
# Representable groupoids in functors, terminology

The shorthand “let `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)` be a groupoid
in functors on `C`” means a representable groupoid in functors.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v

/- Remark 90.21.6: we say “let `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)` be a
groupoid in functors on `C`” to mean that we have a representable groupoid in functors.
Thus `U` and `R` are objects of `C`, there are morphisms `s, t : U ⟶ R`, the pushout of
`s` and `t` exists, there is a morphism `c : R ⟶ pushout s t`, and the coyoneda quintuple
is a groupoid in functors on `C`. -/
@[stacks 06K8] #check (CategoryTheory.GroupoidInFunctors.Representable.spec :
  ∀ {C : Type u} [Category.{v} C] (G : CategoryTheory.GroupoidInFunctors.Representable C),
    HasPushout G.s G.t ∧
      IsGroupoidInFunctors (coyoneda.obj (op G.U)) (coyoneda.obj (op G.R))
        (coyoneda.map G.s.op) (coyoneda.map G.t.op)
        (CategoryTheory.GroupoidInFunctors.Representable.compApp G.s G.t G.c))
