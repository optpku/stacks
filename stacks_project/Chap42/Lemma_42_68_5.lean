/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.OneDimensional
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/- Lemma 42.68.5 (1): the determinant space of a finite-length module over a local ring
has dimension one over the residue field. -/
@[stacks 02P9] #check
  (Module.FiniteLengthDeterminant.finrank_eq_one_of_isFiniteLength R M :
    ∀ hM : IsFiniteLength R M,
      Module.finrank (IsLocalRing.ResidueField R)
        (Module.FiniteLengthDeterminant R M hM) = 1)

/- Lemma 42.68.5 (2): the symbol of any admissible sequence spanning a finite-length
module generates its determinant space over the residue field. -/
@[stacks 02P9] #check
  (Module.FiniteLengthDeterminant.span_symbol_eq_top R M :
    ∀ (hM : IsFiniteLength R M) (e : Module.FiniteLengthDeterminant.Symbol R M hM),
      Submodule.span R (Set.range e.1) = ⊤ →
        Submodule.span (IsLocalRing.ResidueField R)
          {Module.FiniteLengthDeterminant.symbol R M hM e} = ⊤)
