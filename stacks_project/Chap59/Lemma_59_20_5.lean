/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 59.20.5: for each standard topology `τ`, every `τ`-cover of an affine
scheme admits a refinement which is a finite affine standard `τ`-cover. -/
@[stacks 03XA] #check
  (AlgebraicGeometry.StandardTopology.exists_standardCover_refinement :
    ∀ {T : Scheme.{u}} [IsAffine T] (τ : StandardTopology)
      (𝒰 : Scheme.Cover.{v} τ.precoverage T),
      ∃ 𝒱 : AffineFamilyOver T,
        τ.IsCover 𝒱 ∧
          Sieve.ofArrows 𝒱.U 𝒱.map ≤ 𝒰.sieve₀)
