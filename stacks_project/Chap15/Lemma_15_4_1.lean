module

import StacksCheckRecall
public import ReasLib.RingTheory.Filtration.ArtinRees.Perturbation

/-!
# Lemma 15.4.1

@stack 07VE

The reusable perturbation theorems are owned by `LinearMap.IsArtinReesBound` and
`Function.Exact`.
-/

@[expose] public section

/- @stack 07VE -/
@[stacks 07VE "Lemma 15.4.1 (1)"]
#check @LinearMap.IsArtinReesBound.perturb_of_finite_exact

/- @stack 07VE -/
@[stacks 07VE "Lemma 15.4.1 (2)"]
#check @Function.Exact.perturb_of_finite_artinRees

#check @LinearMap.IsArtinReesBound.of_exact_of_congr_mod_pow
#check @Function.Exact.of_congr_mod_pow_and_artinRees
