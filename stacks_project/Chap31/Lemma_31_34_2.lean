/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Composition
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.34.2: let `X` be a quasi-compact and quasi-separated scheme, let `U ⊆ X` be a
quasi-compact open subscheme, let `b : X' ⟶ X` be a `U`-admissible blowup, and let
`b' : X'' ⟶ X'` be admissible over the inverse-image open of `U` on `X'`. Then the composite
`X'' ⟶ X` is a `U`-admissible blowup. -/
@[stacks 080L] #check (AlgebraicGeometry.IsAdmissibleBlowup.comp :
  ∀ {X X' X'' : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U : X.Opens) (hU : QuasiCompact U.ι)
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (b ⁻¹ᵁ U) b'),
    IsAdmissibleBlowup U (b' ≫ b))
