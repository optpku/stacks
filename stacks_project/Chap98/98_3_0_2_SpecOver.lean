/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Spectra of Artinian local algebras over a chosen affine open of `S`. -/
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specOver :
  (Spec (CommRingCat.of Λ) ⟶ S) → ArtinianLocalAlgCat Λ k → Over S)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.specFunctor :
  ∀ (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion],
    ArtinianLocalAlgCat Λ k ⥤ (Over S)ᵒᵖ)
