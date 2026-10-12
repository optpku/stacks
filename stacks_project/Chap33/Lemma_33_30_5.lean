/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.RationalPoint

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.30.5: for a normal variety `X` over a field `k`, an open subscheme `U` of affine
`n`-space over `k`, two `k`-rational points `p` and `q` of `U`, and an invertible module `ℒ` on
`X ×ₖ U`, the restrictions of `ℒ` along `p` and `q` are isomorphic. -/
@[stacks 0BEH] #check
  (AlgebraicGeometry.Scheme.OpenAffineSpace.restrictionModule_iso_of_normalVariety :
    ∀ {k : Type u} [Field k] {n : ℕ}
      (X : Over (Spec (CommRingCat.of k))) [Variety X] (hXnormal : X.left.isNormal)
      (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens)
      (p q : Spec (CommRingCat.of k) ⟶ U.toScheme)
      (hp : p ≫ Scheme.OpenAffineSpace.toBase U = 𝟙 (Spec (CommRingCat.of k)))
      (hq : q ≫ Scheme.OpenAffineSpace.toBase U = 𝟙 (Spec (CommRingCat.of k)))
      (ℒ : (Scheme.OpenAffineSpace.product X U).Modules)
      [Scheme.Modules.Invertible ℒ],
      Nonempty
        (Scheme.OpenAffineSpace.restrictionModule X U p hp ℒ ≅
          Scheme.OpenAffineSpace.restrictionModule X U q hq ℒ))
