/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative perfectness under scalar extension

@stack 0DHW

This leaf combines pseudo-coherence and finite Tor dimension to show that relative perfectness is
preserved around a flat pushout square. The tensor-product theorem is the standard source-facing
specialization. Finite presentation is not needed for either result.
The four rings remain in one universe because `IsPerfectOver` currently fixes its base and algebra
to the same standard derived-category universe; a cross-universe API requires a separate lift
comparison rather than an extra mathematical assumption here.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.DerivedCategory

/-- Relative perfectness passes through any scalar-extension square equipped with the derived
base-change isomorphism comparing its two routes after restriction to the new base ring. -/
@[stacks 0DHW "relative perfectness through a derived base-change isomorphism"]
theorem IsPerfectOver.baseChangeOfIso
    {R A R' A' : Type u}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A']
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K)
    (e :
      (ModuleCat.derivedRestrictionOfScalars (algebraMap R' A')).obj
          ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K) ≅
        (ModuleCat.derivedExtensionOfScalars (algebraMap R R')).obj
          ((ModuleCat.derivedRestrictionOfScalars (algebraMap R A)).obj K)) :
    IsPerfectOver R'
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K) := sorry
/- Proof strategy: use `isPerfectOver_iff`; scalar extension preserves pseudo-coherence, while the
given isomorphism identifies restriction to `R'` with scalar extension of the restricted
finite-Tor-dimensional `R`-object.  Apply the scalar-extension Tor-dimension theorem and transport
both components across `e`. -/

/-- If `A` is flat over `R`, relative perfectness is preserved after base change around a
pushout square from `R` to `R'`. -/
@[stacks 0DHW "relative perfectness around a flat pushout"]
theorem IsPerfectOver.baseChange
    {R A R' A' : Type u}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A'] [Module.Flat R A]
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) :
    IsPerfectOver R'
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K) := sorry
/- Proof strategy: obtain the canonical pushout route isomorphism from
`ModuleCat.DerivedExtension.Pushout`, using flatness of `A` to compute the comparison, and apply
`IsPerfectOver.baseChangeOfIso`. -/

/-- An `R`-perfect complex remains `R'`-perfect after derived extension from `A` to the
tensor-product algebra `A ⊗[R] R'` when `A` is flat over `R`. -/
@[stacks 0DHW "tensor-product base change of relative perfectness"]
theorem IsPerfectOver.tensorBaseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) :
    IsPerfectOver R'
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (A ⊗[R] R'))).obj K) := sorry
/- Proof strategy: instantiate `IsPerfectOver.baseChange` with the canonical tensor-product
pushout square and the right-factor algebra structure on `A ⊗[R] R'`. -/

/-- Lemma 15.84.5 (Stacks `0DHW`): for a flat finitely presented map `R → A`, an
`R`-perfect complex remains `R'`-perfect after derived extension from `A` to `A ⊗[R] R'`. -/
@[stacks 0DHW "base change of a relative-perfect complex"]
theorem IsPerfectOver.tensorBaseChange_of_finitePresentation
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat A)} (hK : IsPerfectOver R K) :
    IsPerfectOver R'
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (A ⊗[R] R'))).obj K) := sorry
/- Proof strategy: apply `hK.tensorBaseChange`; finite presentation is retained solely for the
source-faithful specialization. -/

end CategoryTheory.DerivedCategory
