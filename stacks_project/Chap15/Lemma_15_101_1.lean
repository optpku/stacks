module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.ShortComplex.IdealPower

@[expose] public section

/-!
# Lemma 15.101.1: ideal-power homology comparison

@stack 0EGU
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ShortComplex.IdealPower

/-
Lemma 15.101.1 (0EGU): let `A` be a Noetherian ring, let `I` be an ideal of `A`, and let `S` be
a short complex of finite `A`-modules.  The canonical maps

`H(S) / I ^ (n + 1) H(S) ⟶ H(S / I ^ (n + 1) S)`

have reverse maps after one fixed positive shift.  The two composites are transition maps; hence
the towers are pro-isomorphic and have isomorphic limits.  The quotient-complex homology tower is
Mittag-Leffler, its transition images stabilize uniformly, the comparison kernels and cokernels
are killed by one power of `I`, and the reverse maps can be chosen compatibly with the action of
that power.  All constructions and statements are owned by the reusable short-complex ideal-power
leaf; this file is only the source-facing recall boundary.
-/

/- Canonical stages, towers, and their forward comparison. -/
@[stacks 0EGU "homology stage of an ideal-power quotient short complex"]
#check @stageHomology
@[stacks 0EGU "homology tower of positive ideal-power quotient short complexes"]
#check @tower
@[stacks 0EGU "positive ideal-power quotient tower of ambient homology"]
#check @ambientTower
@[stacks 0EGU "canonical comparison on ideal-power quotient homology stages"]
#check @comparisonApp
@[stacks 0EGU "comparison of ideal-power homology towers"]
#check @comparison
@[stacks 0EGU "canonical limit comparison for ideal-power homology"]
#check @limitComparison
@[stacks 0EGU "finite terms of a short complex"]
#check @FiniteTerms

/- Part (1): a single shifted reverse comparison and its pro-categorical consequence. -/
@[stacks 0EGU "shifted reverse ideal-power homology comparison"]
#check @Comparison.Shift
@[stacks 0EGU "constant-shift inverse for sequential pro-objects"]
#check @Pro.SequentialHom.IsShiftInverse
@[stacks 0EGU "shift inverse for ideal-power homology towers"]
#check @FiniteTerms.existsShift
@[stacks 0EGU "canonical pro-morphism for ideal-power homology"]
#check @Comparison.proMap
@[stacks 0EGU "pro-isomorphism for ideal-power homology towers"]
#check @FiniteTerms.proMap_isIso

/- Part (2): the canonical inverse-limit comparison. -/
@[stacks 0EGU "canonical limit isomorphism from an explicit finite-terms hypothesis"]
#check @FiniteTerms.limitIso
@[stacks 0EGU "forward map of the finite-terms limit isomorphism"]
#check @FiniteTerms.limitIso_hom

/- Parts (3) and (4): Mittag-Leffler and uniform image stabilization. -/
@[stacks 0EGU "Mittag-Leffler ideal-power homology tower"]
#check @FiniteTerms.towerIsMittagLeffler
@[stacks 0EGU "stabilized image of ideal-power quotient homology"]
#check @Comparison.ImageStabilizes
@[stacks 0EGU "uniform image stabilization for ideal-power homology"]
#check @FiniteTerms.existsImageStabilization

/- Part (5): one bound for all comparison kernels and cokernels. -/
@[stacks 0EGU "kernel bound for ideal-power homology comparison"]
#check @Comparison.HasKernelBound
@[stacks 0EGU "cokernel bound for ideal-power homology comparison"]
#check @Comparison.HasCokernelBound
@[stacks 0EGU "uniform kernel-cokernel bound for ideal-power homology"]
#check @Comparison.HasUniformBound
@[stacks 0EGU "uniform annihilation for ideal-power homology comparison"]
#check @FiniteTerms.existsUniformBound

/- Part (6): compatibility on the `I ^ c`-part of each shifted stage. -/
@[stacks 0EGU "quotient of the ambient-to-stage homology map"]
#check @Comparison.toStageQuotient
@[stacks 0EGU "power compatibility for shifted ideal-power homology comparison"]
#check @Comparison.PowerCompatible
@[stacks 0EGU "power-compatible shift inverse for ideal-power homology"]
#check @FiniteTerms.existsPowerCompatible

/- The six source clauses, checked at their complete expected types. -/
section SourceStatement

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
variable (h : FiniteTerms S)

@[stacks 0EGU "shift inverse for ideal-power homology towers"]
#check (FiniteTerms.existsShift S I h :
  ∃ c : ℕ, 0 < c ∧ ∃ β : Comparison.Shift S I c,
    Pro.SequentialHom.IsShiftInverse (comparison S I) c β)

@[stacks 0EGU "pro-isomorphism for ideal-power homology towers"]
#check (FiniteTerms.proMap_isIso S I h : IsIso (Comparison.proMap S I))

@[stacks 0EGU "canonical limit isomorphism from finite short-complex terms"]
#check (FiniteTerms.limitIso S I h : limit (ambientTower S I) ≅ limit (tower S I))

@[stacks 0EGU "Mittag-Leffler ideal-power homology tower"]
#check (FiniteTerms.towerIsMittagLeffler S I h : (tower S I).IsMittagLeffler)

@[stacks 0EGU "uniform image stabilization for ideal-power homology"]
#check (FiniteTerms.existsImageStabilization S I h :
  ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, Comparison.ImageStabilizes S I c n)

@[stacks 0EGU "uniform annihilation for ideal-power homology comparison"]
#check (FiniteTerms.existsUniformBound S I h :
  ∃ c : ℕ, 0 < c ∧ Comparison.HasUniformBound S I c)

@[stacks 0EGU "power-compatible shift inverse for ideal-power homology"]
#check (FiniteTerms.existsPowerCompatible S I h :
  ∃ c : ℕ, 0 < c ∧ ∃ β : Comparison.Shift S I c,
    Pro.SequentialHom.IsShiftInverse (comparison S I) c β ∧
      ∀ n : ℕ, Comparison.PowerCompatible S I c β n)

end SourceStatement

#print axioms CategoryTheory.ShortComplex.IdealPower.Comparison.proMap
#print axioms CategoryTheory.ShortComplex.IdealPower.Comparison.toStageQuotient
