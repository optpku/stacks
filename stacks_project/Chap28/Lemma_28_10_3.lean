/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.10.3: Let `Y` be an irreducible closed subset of a scheme `X`, and let `ξ` be
its generic point. The equality `closure {ξ} = Y` identifies the codimension of `Y` in `X`
with `Order.coheight ξ`; symmetry of the following pointwise equality gives
`codim(Y, X) = ringKrullDim (X.presheaf.stalk ξ)`. -/
@[stacks 02IZ] #check
  (AlgebraicGeometry.ringKrullDim_stalk_eq_coheight :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X),
      ringKrullDim (X.presheaf.stalk x) = Order.coheight x)
