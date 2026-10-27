/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChange
public import ReasLib.RingTheory.AdicCompletion.Idempotence
import StacksCheckRecall

/-! # Base change equivalence for affine modification categories -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong

universe u

/- Lemma 88.30.1: A homomorphism of Noetherian rings inducing an isomorphism
on adic completions gives an equivalence by base change on locally finite type
algebraic spaces that are isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0AE5] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.isEquivalence_sourceBaseChangeAlgebraMap :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A),
    Function.Bijective
      (AdicCompletion.extensionMap I :
        AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B) →
    (sourceBaseChangeAlgebraMap B hA I).IsEquivalence)

/- The canonical map on completions is bijective when the target is the
adic completion of a Noetherian ring. -/
#check (AdicCompletion.bijective_extensionMap_adicCompletion :
  ∀ {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A),
    Function.Bijective
      (AdicCompletion.extensionMap I :
        AdicCompletion I A →+*
          AdicCompletion (I.map (algebraMap A (AdicCompletion I A)))
            (AdicCompletion I A)))
