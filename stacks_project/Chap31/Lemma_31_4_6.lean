/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints.Quotient

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Set TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 31.4.6: a coherent module on a locally Noetherian scheme has a maximal coherent
nowhere-dense subobject whose quotient has the same support, has no embedded associated
points, and agrees with the original module on a suitable dense open. -/
@[stacks 02OL] #check
  (AlgebraicGeometry.Scheme.Modules.exists_maximal_isCoherentNowhereDenseSubobject_with_cokernel_properties :
    ∀ {X : Scheme.{u}} (F : X.Modules) [IsLocallyNoetherian X] [F.IsCoherent],
      ∃ K : Subobject F,
        Maximal (AlgebraicGeometry.Scheme.Modules.IsCoherentNowhereDenseSubobject F) K ∧
          AlgebraicGeometry.Scheme.Modules.moduleSupport (cokernel K.arrow) =
              AlgebraicGeometry.Scheme.Modules.moduleSupport F ∧
            AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints (cokernel K.arrow) =
                (∅ : Set X) ∧
              ∃ U : X.Opens,
                Dense (U : Set X) ∧
                  Dense
                    (Subtype.val ⁻¹' (U : Set X) :
                      Set (AlgebraicGeometry.Scheme.Modules.moduleSupport F)) ∧
                    Nonempty ((cokernel K.arrow).restrict U.ι ≅ F.restrict U.ι))
