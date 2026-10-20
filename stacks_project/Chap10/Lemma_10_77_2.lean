module

public import ReasLib.Algebra.Module.Projective.Ext
import StacksCheckRecall

/-!
# Lemma 10.77.2

The direct-summand and degree-one `Ext` characterizations of projectivity are
recalled from their reusable `Module.Projective` owners.

@stack 05CF
-/

@[expose] public section

open CategoryTheory

universe u v

section

variable {R : Type u} [Ring R] [Small.{v} R]
variable (P : Type v) [AddCommGroup P] [Module R P]

/- Lemma 10.77.2: projectivity is equivalent both to splitting off from a free module and to
vanishing of `Ext¹(P, -)`.  The two equivalences are exposed separately by the canonical API. -/
@[stacks 05CF]
#check (Module.Projective.iff_subsingleton_ext_one (R := R) P :
  Module.Projective R P ↔
    ∀ Y : ModuleCat.{v} R,
      Subsingleton (Abelian.Ext (ModuleCat.of R P) Y 1))

#check @Module.Projective.iff_split'

end
