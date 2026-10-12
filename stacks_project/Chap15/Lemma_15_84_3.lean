/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect.Tensor
import StacksCheckRecall

/-!
# Lemma 15.84.3

@stack 0DHU
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 15.84.3 (1), tag `0DHU`: if `R → A` is flat and finitely presented, then every perfect
object of `D(A)` is perfect relative to `R`. -/
@[stacks 0DHU "(1)"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) =>
  (hK.isPerfectOver_of_flat_of_finitePresentation (R := R) : K.IsPerfectOver R)

/- Lemma 15.84.3 (2), tag `0DHU`: under the same flat finite-presentation setup, tensoring an
`R`-perfect object by a perfect `A`-complex preserves relative perfectness. -/
@[stacks 0DHU "(2)"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K M : DerivedCategory (ModuleCat A)} (hK : K.IsPerfect) (hM : M.IsPerfectOver R) =>
  (hK.tensor_isPerfectOver_of_flat_of_finitePresentation hM :
    (DerivedCategory.DerivedTensor.Bifunctor.obj K M).IsPerfectOver R)

/- The reusable conclusions hold under weaker hypotheses. -/
#check @DerivedCategory.IsPerfect.isPerfectOver
#check @DerivedCategory.IsPerfect.tensor_isPerfectOver

end
