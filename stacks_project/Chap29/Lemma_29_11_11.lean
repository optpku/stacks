/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

open AlgebraicGeometry

universe u

/-
Lemma 29.11.11: for a global section of an invertible module on a scheme, the inclusion of its
nonvanishing open is an affine morphism.
-/
@[stacks 01SF] #check
  (@AlgebraicGeometry.Scheme.Modules.Invertible.isAffineHom_ι_sectionNonvanishingOpen :
    ∀ {X : Scheme.{u}} {L : X.Modules} [hL : Scheme.Modules.Invertible L]
      (s : Γ(L, ⊤)), IsAffineHom (hL.sectionNonvanishingOpen s).ι)
