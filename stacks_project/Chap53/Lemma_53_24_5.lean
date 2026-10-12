/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.StableDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

/- Lemma 53.24.5 -/
@[stacks 0E3P] #check
  (AlgebraicGeometry.SchemeOverField.curveDualizingModule_isAmple_of_stable :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension hΓ),
      Scheme.Modules.isAmpleObject
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
          X.hom))
