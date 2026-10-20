module

public import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

section Pullback

variable {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [Epi f]

/- Lemma 12.5.14 (1): epimorphisms are stable under pullback in an abelian category. -/
@[stacks 05PK] #check
  (Abelian.epi_pullback_of_epi_f f g : Epi (pullback.snd f g))

end Pullback

section Pushout

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [Mono f]

/- Lemma 12.5.14 (2): monomorphisms are stable under pushout in an abelian category. -/
#check
  (Abelian.mono_pushout_of_mono_f f g : Mono (pushout.inr f g))

end Pushout

end CategoryTheory
