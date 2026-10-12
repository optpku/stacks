/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.SquareZeroLift.Presentation
import StacksCheckRecall

@[expose] public section

/-!
# Presentation classes detected by the square-zero obstruction

`SquareZeroLift.theta` is the actual map from `H₂(A / IA)` to `S / IS`: it composes the
homology map induced by the lifted differential obstruction with the canonical quotient
augmentation.  `LiftedRelation.obstruction` is the concrete presentation class detected by that
map.
-/

/- Lemma 23.7.2 (Tag 09PT): realization of the lifted-relation obstruction by a class in
`H₂(A / IA)`. -/
open RingHom.SquareZeroExtension

universe u v w x y

section

variable {R' R : Type u} [CommRing R'] [CommRing R]
variable {S : Type y} [CommRing S] [Algebra R S]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {generators : ℕ → Type v}
variable {A : DividedPowerChainAlgebra.{u, y} R}
variable {g : RingHom.SquareZeroExtension.Generator f}
variable {P : A.toGradedAlgebra.FreePresentation generators}
variable {ι : Type w} {σ : Type x} [Fintype σ]
variable (L : A.SquareZeroLift g P)
variable (h_finite : ∀ n : ℕ, Finite (generators n))
variable (augmentation : ChainDGAlgebra.Augmentation A.toChainDGAlgebra S)
variable (hH0 : Function.Bijective augmentation.homologyZeroMap)
variable (hH1 : CategoryTheory.Limits.IsZero (A.toChainDGAlgebra.homology 1))
variable {Q : Algebra.Presentation R S ι σ}
variable (relation : Algebra.Presentation.LiftedRelation g Q)

@[stacks 09PT "Lemma 23.7.2"]
#check (DividedPowerChainAlgebra.SquareZeroLift.exists_homologyClass_of_finite
    L h_finite augmentation hH0 hH1 relation :
  ∃ ξ : (A.annihilatorQuotient (f := f)).homology 2,
    L.theta augmentation ξ = relation.obstruction)

end

#check @Algebra.Presentation.LiftedRelation
#check @Algebra.Presentation.LiftedRelation.obstruction
#check @DividedPowerChainAlgebra.SquareZeroLift.theta
#check @DividedPowerChainAlgebra.SquareZeroLift.exists_homologyClass
#check @DividedPowerChainAlgebra.SquareZeroLift.exists_lift_and_homologyClass
