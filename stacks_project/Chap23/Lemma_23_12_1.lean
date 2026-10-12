/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Tate
import StacksCheckRecall

@[expose] public section

/-!
# Powered Koszul--Tate approximations

The reusable owner fixes the exact-power Koszul chain DGAs and their canonical transitions, equips
the whole system with explicit canonical compatible divided powers, and constructs the canonical
augmentation to `R ⧸ Ideal.powerSpan f n`. A finite approximation records a positive exponent
`N ≥ n`, a finite-positive-generator Tate resolution of the `N`th power quotient, comparison maps
`K_N ⟶ A ⟶ K_n`, the two canonical composite conditions, `A₀ = R`, a genuine quasi-isomorphic
augmentation, and the induced finite-power quotient map on zeroth homology.

The canonical Koszul divided powers are explicit standard-basis data in the reusable owner. Only
existence of a finite Tate approximation remains proposition-valued; no chapter declaration
chooses such an approximation by `Classical.choice`.
-/

/- Lemma 23.12.1 (Tag 0GZ4): over a Noetherian ring, every positive exact-power Koszul stage has
a finite divided-power Tate approximation from some later exact-power stage. -/
universe u x

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {ι : Type u} [Finite ι]
variable (f : ι → R) (n : ℕ+)

@[stacks 0GZ4 "powered Koszul--Tate approximation"]
#check (KoszulComplex.Tate.Approximation.nonempty_canonical (R := R) f n :
  Nonempty (KoszulComplex.Tate.Approximation.{u, x}
    (KoszulComplex.DP.system f) n))

end

#check @KoszulComplex.DP.system
#check @KoszulComplex.DP.stage
#check @KoszulComplex.DP.transition
#check @KoszulComplex.DP.tower
#check @KoszulComplex.PowerQuotient.presentation
#check @KoszulComplex.PowerQuotient.presentation_surjective
#check @KoszulComplex.Tate.Resolution
#check @KoszulComplex.Tate.Approximation
#check @KoszulComplex.Tate.FromKoszul.IsCanonical
#check @KoszulComplex.Tate.Comparison.FactorsTransition
#check @KoszulComplex.Tate.ToKoszul.InducesQuotient
#check @KoszulComplex.Tate.Approximation.degreeZeroIsBase
#check @KoszulComplex.Tate.Approximation.augmentation_quasiIso
#check @KoszulComplex.ChainDGA.augmentation
#check @KoszulComplex.ChainDGA.homologyZeroMap_bijective
#check @Ideal.powerSpan
#check @Ideal.powerQuotientMap
#check @TateResolution.HasFinitePositiveGenerators
