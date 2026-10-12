/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.Flat
import StacksCheckRecall

@[expose] public section

/-!
@stack 00MB

# Flatness and exactness of Noetherian completion
-/

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

/- Lemma 10.97.2 (1): the canonical ring map from a Noetherian ring to its
`I`-adic completion is flat. -/
@[stacks 00MB "(1)"]
#check (RingHom.flat_algebraMap_iff.mpr
    (inferInstance : Module.Flat R (AdicCompletion I R)) :
  (algebraMap R (AdicCompletion I R)).Flat)

section exact

variable {M N P : Type u}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N]
variable [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
variable (hf : Function.Injective f) (hfg : Function.Exact f g)
variable (hg : Function.Surjective g)

/- Lemma 10.97.2 (2): completion is exact on short exact sequences of
finitely generated modules over a Noetherian ring. -/
@[stacks 00MB "(2)"]
#check (map_exact (I := I) hf hfg hg :
  Function.Exact (map I f) (map I g))

end exact
end AdicCompletion
