/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Sections

/-!
# Lemma 27.3.3 compatibility entry point

Composition of affine-spectrum maps induced by section restriction belongs to
the neutral section-ring API.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 27.3.3: compatibility of affine-spectrum maps with successive restrictions. -/
@[stacks 01LO] #check
  (AlgebraicGeometry.Scheme.specMap_qcAlgebraSectionRestrict_comp :
    {S : Scheme.{u}} → (A : S.QcAlgebraUnder) → {U U' U'' : S.Opens} →
      (hU : IsAffineOpen U) → (hU' : IsAffineOpen U') →
        (hU'' : IsAffineOpen U'') → (h : U ≤ U') → (h' : U' ≤ U'') →
          Spec.map (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A h) ≫
              Spec.map (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A h') =
            Spec.map
              (AlgebraicGeometry.Scheme.qcAlgebraSectionRestrict A (h.trans h')))
