/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Perfect
import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.84.5: relative perfectness under base change

@stack 0DHW

The reusable owner is `DerivedCategory.IsPerfectOver.tensorBaseChange`. It only assumes that
`R → A` is flat: the finite-presentation hypothesis in the source is part of the section setup,
but is unnecessary for preservation of relative perfectness.
-/

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/- Lemma 15.84.5, Stacks `0DHW`: if `R → A` is flat and of finite presentation, `R → R'`
is a ring map, and `K : D(A)` is `R`-perfect, then
`K ⊗[A]^L[A ⊗[R] R']` is `R'`-perfect. -/
@[stacks 0DHW "base change of a relative-perfect complex"]
#check fun {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPerfectOver R) =>
  (hK.tensorBaseChange_of_finitePresentation (R' := R') :
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (A ⊗[R] R'))).obj K).IsPerfectOver R')

/- The canonical owner does not retain the redundant finite-presentation assumption. -/
#check @DerivedCategory.IsPerfectOver.tensorBaseChange

/- The pushout form supports base-change rings presented independently of a tensor-product model. -/
#check @DerivedCategory.IsPerfectOver.baseChange

/- The comparison-isomorphism form also applies to Tor-independent scalar-extension squares. -/
#check @DerivedCategory.IsPerfectOver.baseChangeOfIso

/- The two property-level scalar-extension results used by the owner. -/
#check @DerivedCategory.HasTorAmplitudeIn.extension
#check @DerivedCategory.HasFiniteTorDimension.extension

end
