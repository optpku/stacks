module

public import ReasLib.RingTheory.GlobalDimension.Localization.AtPrime
import StacksCheckRecall

/-!
# Detecting a Global-Dimension Bound at Maximal Ideals

@stack 00O9
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ)

/- Lemma 10.110.2 (Stacks `00O9`): a commutative Noetherian ring has global dimension at most the
fixed bound `n` if and only if every maximal localization has global dimension at most `n`. -/
@[stacks 00O9]
#check (HasGlobalDimensionLE.iff_forall_atMaximal (R := R) n :
  HasGlobalDimensionLE R n ↔
    ∀ m : MaximalSpectrum R,
      HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n)

/- The prime-local and existential finite-global-dimension formulations are canonical companions
to the fixed maximal-local bound in the source. -/
#check @HasGlobalDimensionLE.iff_forall_atPrime
#check @IsFiniteGlobalDimensionRing.iff_exists_uniform_atMaximal
#check @IsFiniteGlobalDimensionRing.iff_exists_uniform_atPrime
