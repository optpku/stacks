/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Fpqc

/-!
# Morphism properties under affine base change

A homomorphism of Noetherian rings inducing an isomorphism on adic completions
preserves and reflects fpqc-local morphism properties containing identities
on locally finite type algebraic spaces that are isomorphisms away from the
ideal's vanishing locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects every fpqc-local-on-the-target
morphism property containing identities on structure morphisms of locally finite
type algebraic spaces that are isomorphisms away from the ideal's vanishing locus. -/
theorem sourceBaseChangeAlgebraMap_morphismProperty_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (fpqcPrecoverage S)] [P.ContainsIdentities]
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    P Y.obj.hom ↔ P ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects quasi-compactness of
structure morphisms of locally finite type algebraic spaces that are
isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_quasiCompact_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    QuasiCompact Y.obj.hom ↔
      QuasiCompact ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects quasi-separatedness of
structure morphisms of locally finite type algebraic spaces that are
isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_quasiSeparated_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    QuasiSeparated Y.obj.hom ↔
      QuasiSeparated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects separatedness of
structure morphisms of locally finite type algebraic spaces that are
isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_separated_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    Separated Y.obj.hom ↔
      Separated ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects properness of
structure morphisms of locally finite type algebraic spaces that are
isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_proper_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    Proper Y.obj.hom ↔
      Proper ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

/-- For a homomorphism of Noetherian rings inducing a bijection on adic
completions, affine base change preserves and reflects finiteness of
structure morphisms of locally finite type algebraic spaces that are
isomorphisms away from the ideal's vanishing locus. -/
@[stacks 0BH5]
theorem sourceBaseChangeAlgebraMap_isFinite_iff {A : Type u} (B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A)
    (h_completion :
      Function.Bijective
        (AdicCompletion.extensionMap I :
          AdicCompletion I A →+* AdicCompletion (I.map (algebraMap A B)) B))
    (Y : Source (specOver hA) (zeroLocusPoints hA I)) :
    IsFinite Y.obj.hom ↔
      IsFinite ((sourceBaseChangeAlgebraMap B hA I).obj Y).obj.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
