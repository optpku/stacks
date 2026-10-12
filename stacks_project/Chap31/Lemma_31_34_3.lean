/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Extension

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 31.34.3: let `X` be a quasi-compact and quasi-separated scheme, let `U, V ⊆ X` be
quasi-compact open subschemes, and let `b : V' ⟶ V` be a `(U ∩ V)`-admissible blowup. Then
there exists a `U`-admissible blowup `π : X' ⟶ X` whose restriction to `V` is isomorphic to
`b` over `V`. -/
@[stacks 080M] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter :
    ∀ {X V' : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U V : X.Opens) (hU : QuasiCompact U.ι) (hV : QuasiCompact V.ι)
      (b : V' ⟶ V.toScheme),
      AlgebraicGeometry.IsAdmissibleBlowup (V.ι ⁻¹ᵁ U) b →
        ∃ (X' : AlgebraicGeometry.Scheme.{u}) (π : X' ⟶ X),
          AlgebraicGeometry.IsAdmissibleBlowup U π ∧
            Nonempty (Over.mk (π ∣_ V) ≅ Over.mk b))
