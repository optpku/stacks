module

public import ReasLib.RingTheory.MvPolynomial.ClosedPoints
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.25.5: every nonempty open subset of affine `d`-space over a field contains a
closed point whose residue field is finite and separable over the field. -/
@[stacks 055T]
#check (MvPolynomial.exists_closedPoint_mem_open_finiteSeparableResidueField :
  ∀ {k : Type u} [Field k] (d : ℕ)
    (W : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin d) k)))
    (_ : W ≠ ⊥),
    ∃ (w : W) (_ : w.1 ∈ closedPoints (PrimeSpectrum (MvPolynomial (Fin d) k))),
      FiniteDimensional k w.1.asIdeal.ResidueField ∧
        Algebra.IsSeparable k w.1.asIdeal.ResidueField)
