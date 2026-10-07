module

public import stacks_project.Chap64.Lemma_64_18_2_Reduction
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Lemma 64.18.2: on a Noetherian scheme X, an inverse system {G_n}_{n ≥ 1} of
constructible ZMod (ℓ^n)-modules whose reductions G_n / ℓ^k G_n are eventually
constant for every k ≥ 1 has eventual values F_k assembling into a ℤ_[ℓ]-sheaf. -/
@[stacks 03UN] #check ZEllSheaf.ofEventuallyConstant
