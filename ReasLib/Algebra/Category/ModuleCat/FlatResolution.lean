module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel
import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatRepresentative

/-!
# Finite flat resolutions of modules

@stack 066F

This file owns the elementary resolution presentation of a finite Tor-dimension bound.  The
derived Tor-amplitude predicate remains the canonical homological owner; the explicit resolution
predicate is its reusable module-theoretic presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {R : Type u} [CommRing R]

/-- An `R`-module has a finite flat resolution of length at most `d`. -/
@[stacks 066F "finite flat resolution"]
def HasFiniteFlatResolutionLengthLE (M : ModuleCat R) : ℕ → Prop
  | 0 => Module.Flat R M
  | n + 1 =>
      ∃ (F : Fin (n + 2) → ModuleCat R),
        (∀ i, Module.Flat R (F i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → F i.succ ⟶ F i.castSucc) (π : F 0 ⟶ M),
            Function.Surjective π ∧ Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
                Function.Injective (δ (Fin.last n))

/-- A finite flat resolution of length at most zero is exactly flatness. -/
@[stacks 066F "finite flat resolution of length zero"]
theorem hasFiniteFlatResolutionLengthLE_zero_iff (M : ModuleCat R) :
    HasFiniteFlatResolutionLengthLE M 0 ↔ Module.Flat R M := sorry
/- Proof strategy: unfold `HasFiniteFlatResolutionLengthLE` at zero. -/

/-- Lemma 15.67.6 (Stacks `066F`): Tor dimension at most `d` is equivalent to the existence of
a flat resolution of length at most `d`. -/
@[stacks 066F "Tor dimension and finite flat resolutions"]
theorem hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE (M : ModuleCat R) (d : ℕ) :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M d ↔
      HasFiniteFlatResolutionLengthLE M d := sorry
/- Proof strategy: use the finite-interval flat representative theorem in one direction and
truncate a projective resolution at degree `-d`, applying the flat cutoff-cokernel criterion in
the other direction. -/

/-- A Tor-dimension bound supplies a finite flat resolution of the same length. -/
@[stacks 066F "Tor dimension gives a finite flat resolution"]
theorem HasTorDimensionLE.hasFiniteFlatResolutionLengthLE {M : ModuleCat R} {d : ℕ}
    (hM : DerivedCategory.DerivedTensor.HasTorDimensionLE M d) :
    HasFiniteFlatResolutionLengthLE M d := sorry
/- Proof strategy: apply the forward implication of
`hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`. -/

/-- A finite flat resolution supplies the corresponding Tor-dimension bound. -/
@[stacks 066F "finite flat resolution gives Tor dimension"]
theorem HasFiniteFlatResolutionLengthLE.hasTorDimensionLE {M : ModuleCat R} {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M d := sorry
/- Proof strategy: apply the reverse implication of
`hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`. -/

/-- An `R`-module has Tor dimension at most zero exactly when it is flat. -/
@[stacks 066F "Tor dimension zero"]
theorem hasTorDimensionLE_zero_iff_flat (M : ModuleCat R) :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M 0 ↔ Module.Flat R M := sorry
/- Proof strategy: compose `hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE` at zero with
`hasFiniteFlatResolutionLengthLE_zero_iff`. -/

end CategoryTheory.ModuleCat
