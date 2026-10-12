/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing.EtaleCover

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.38.8: every smooth morphism admits an affine étale cover whose maps to the
base factor through affine schemes by smooth morphisms with sections and geometrically
connected fibres, followed by étale morphisms. -/
@[stacks 0EY4] #check
  (AlgebraicGeometry.Smooth.exists_affineEtaleCover_factorization :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Smooth f],
      ∃ 𝒰 : X.AffineCover (@AlgebraicGeometry.Etale), ∀ i : 𝒰.I₀,
        ∃ (V : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsAffine V)
          (p : 𝒰.cover.X i ⟶ V) (q : V ⟶ S)
          (_ : AlgebraicGeometry.Smooth p) (_ : AlgebraicGeometry.Etale q)
          (s : V ⟶ 𝒰.cover.X i) (_ : s ≫ p = 𝟙 V)
          (_ : AlgebraicGeometry.GeometricallyConnected p),
          p ≫ q = 𝒰.cover.f i ≫ f)
