/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FlatLocalBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.completionAlong

universe u

/- Lemma 88.30.3: A flat local map `A → B` of local Noetherian rings
preserving the maximal ideal and inducing a bijection on residue fields gives
an equivalence by base change between the categories of locally finite type
algebraic spaces that are isomorphisms away from the closed points. The
maximal-ideal equality identifies the target's extended ideal with the maximal
ideal of `B`. Taking `hA` to be the identity of `Spec(A)` recovers the source
categories. -/
@[stacks 0AF7] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlong.isEquivalence_sourceBaseChangeAlgebraMap_of_flat :
    ∀ {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    [IsNoetherianRing B] [Module.Flat A B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S),
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B →
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) →
    (sourceBaseChangeAlgebraMap B hA (IsLocalRing.maximalIdeal A)).IsEquivalence)
