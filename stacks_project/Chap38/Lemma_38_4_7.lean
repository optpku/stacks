/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking

variable {S : Scheme.{u}} {X : Over S} {ℱ : X.left.Modules}
  [LocallyOfFiniteType X.hom] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] {x : X.left}

/- Lemma 38.4.7 (1): restricting to a prescribed standard-open neighbourhood
of the base point gives a standard shrinking whose four opens are the corresponding
inverse images. -/
@[stacks 05HA]
#check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking.existsOfBase :
    ∀ (D : OneStepDevissageAtAmbientPoint X ℱ x) (S' : S.Opens)
      (a : Γ(S, ⊤)), S' = S.basicOpen a → X.hom x ∈ S' →
        ∃ W : D.StandardShrinking,
          W.base = S' ∧
            W.source = X.hom ⁻¹ᵁ S' ∧
            W.auxiliary = D.toOneStepDevissage.Z.hom ⁻¹ᵁ S' ∧
            W.model = D.toOneStepDevissage.Y.hom ⁻¹ᵁ S')

/- Lemma 38.4.7 (2): any standard-open neighbourhood of the distinguished model
point becomes the model open of a standard shrinking after restriction over its base. -/
@[stacks 05HA]
#check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking.existsWithModel :
    ∀ (D : OneStepDevissageAtAmbientPoint X ℱ x)
      (V : D.toOneStepDevissage.Y.left.Opens)
      (a : Γ(D.toOneStepDevissage.Y.left, ⊤)),
      V = D.toOneStepDevissage.Y.left.basicOpen a → D.y ∈ V →
        ∃ W : D.StandardShrinking,
          W.model = V ⊓ (D.toOneStepDevissage.Y.hom ⁻¹ᵁ W.base))

/- Lemma 38.4.7 (3): every open neighbourhood of the distinguished source point
contains the source open of a standard shrinking. -/
@[stacks 05HA]
#check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking.existsSourceLE :
    ∀ (D : OneStepDevissageAtAmbientPoint X ℱ x) (U : X.left.Opens),
      x ∈ U → ∃ W : D.StandardShrinking, W.source ≤ U)

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking
