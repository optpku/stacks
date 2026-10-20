module

public import Mathlib.Algebra.Homology.SingleHomology
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of augmented chain DGAs

An ordinary algebra placed in degree zero has no positive homology.  Consequently, a chain DGA
with a quasi-isomorphic augmentation to an ordinary algebra is positive-acyclic.  The result is
stated for arbitrary augmentations, independently of Tate resolutions and divided powers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The chain DGA associated with an ordinary algebra concentrated in degree zero has vanishing
positive homology. -/
@[stacks 09PQ "positive homology of an algebra concentrated in degree zero"]
theorem ofAlgebra_positiveHomologyVanishes
    (S : Type v) [CommRing S] [Algebra R S] :
    (ofAlgebra R S).PositiveHomologyVanishes := sorry

namespace Augmentation

variable {A : ChainDGAlgebra.{u, v} R}
variable {S : Type v} [CommRing S] [Algebra R S]

/-- Tag 09PQ: a quasi-isomorphic augmentation to an ordinary algebra forces all positive
homology of the source chain DGA to vanish. -/
@[stacks 09PQ "positive acyclicity from a quasi-isomorphic augmentation"]
theorem positiveHomologyVanishes (augmentation : Augmentation A S)
    [QuasiIso augmentation.toChainMap] : A.PositiveHomologyVanishes := sorry

end Augmentation

end ChainDGAlgebra
