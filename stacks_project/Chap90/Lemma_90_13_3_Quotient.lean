/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Quotient

/-!
# Quotients of residue-identified Artinian local algebras

The categorical quotient and its factor map are supplied by their shared owner.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.quotient :
  ∀ (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier), ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.quotientFactor :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom),
    B.quotient J (hJ.trans (ArtinianLocalAlgCat.ker_le_maximal f)) ⟶ A)
