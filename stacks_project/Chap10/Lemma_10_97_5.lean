module

public import ReasLib.RingTheory.AdicCompletion.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
@stack 05GH

# Noetherianity and completeness from a Noetherian quotient
-/

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing (R ⧸ I)] (hI : I.FG)

/- Lemma 10.97.5 (1): if `R ⧸ I` is Noetherian and `I` is finitely generated, then the
`I`-adic completion of `R` is Noetherian. -/
@[stacks 05GH "(1)"]
#check (isNoetherianRing I hI : IsNoetherianRing (AdicCompletion I R))

/- Lemma 10.97.5 (2): under the same hypotheses, the completion is complete for the extended
ideal `I.map (algebraMap R (AdicCompletion I R))`. -/
@[stacks 05GH "(2)"]
#check (isAdicComplete_self I hI :
  IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R))

#check (quotientExtensionEquiv I hI :
  (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ I)
#check @IsAdicComplete.isNoetherianRing

end AdicCompletion

#check @adicCompletion_isNoetherian_and_isAdicComplete
