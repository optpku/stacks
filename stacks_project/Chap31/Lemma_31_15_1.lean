/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.RegularSection

universe u

/- Lemma 31.15.1: Let `X` be a locally Noetherian scheme, `ℒ` an invertible
`O_X`-module, and `s` a global section of `ℒ`. Then `s` is regular if and only if it does not
vanish at any associated point of `X`. -/
@[stacks 0AYL] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.isRegularSection_iff_associatedPoints_subset_sectionNonvanishingLocus :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] (s : ℒ.sections),
      AlgebraicGeometry.RingedSpace.IsRegularSection ℒ s ↔
        X.associatedPoints ⊆
          AlgebraicGeometry.RingedSpace.sectionNonvanishingLocus X.toRingedSpace ℒ s)
