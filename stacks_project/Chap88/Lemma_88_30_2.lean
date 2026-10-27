/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChangeProperties
import StacksCheckRecall

/-!
# Transfer of morphism properties under affine base change

With the notation and assumptions of Lemma 88.30.1, corresponding structure
morphisms under canonical affine base change are quasi-compact, quasi-separated,
separated, proper, or finite if and only if their counterparts are so.
More generally, this holds for every fpqc-local-on-the-target morphism property
containing identities.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong

universe u

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_morphismProperty_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (fpqcPrecoverage S)] [P.ContainsIdentities]
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    P Y.obj.hom ↔ P ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)

/- Lemma 88.30.2: A homomorphism of Noetherian rings inducing an isomorphism
on adic completions preserves and reflects quasi-compactness, quasi-separatedness,
separatedness, properness and finiteness under canonical base change on locally
finite type algebraic spaces that are isomorphisms away from the ideal's
vanishing locus. -/
@[stacks 0BH5] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_quasiCompact_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    QuasiCompact Y.obj.hom ↔
      QuasiCompact ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_quasiSeparated_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    QuasiSeparated Y.obj.hom ↔
      QuasiSeparated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_separated_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    Separated Y.obj.hom ↔
      Separated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_proper_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    Proper Y.obj.hom ↔
      Proper ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChangeAlgebraMap_isFinite_iff :
  ∀ {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)),
    IsFinite Y.obj.hom ↔
      IsFinite ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom)
