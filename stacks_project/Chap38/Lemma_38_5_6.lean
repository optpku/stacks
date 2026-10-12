/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.StandardShrinking.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

open AlgebraicGeometry Scheme.Modules

/- Lemma 38.5.6 (1): restricting to a prescribed standard-open neighbourhood
of the base point gives a standard shrinking whose source and all stage opens
are the corresponding inverse images. -/
@[stacks 05HM] #check
  (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking.existsOfBase :
    ∀ {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
      [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
      (D : CompleteDevissageAtAmbientPoint f F x) (S' : S.Opens)
      (a : Γ(S, ⊤)), S' = S.basicOpen a → f x ∈ S' →
      ∃ W : D.StandardShrinking,
        W.base = S' ∧
          W.source = f ⁻¹ᵁ S' ∧
          (∀ k, W.auxiliary k =
            (D.toCompleteDevissageOver.stage k).Z.hom ⁻¹ᵁ S') ∧
          ∀ k, W.model k =
            (D.toCompleteDevissageOver.stage k).Y.hom ⁻¹ᵁ S')

/- Lemma 38.5.6 (2): a standard-open neighbourhood of the terminal model
point becomes the terminal model open after restriction over the resulting
common base. -/
@[stacks 05HM] #check
  (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking.existsWithTerminalModel :
    ∀ {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
      [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
      (D : CompleteDevissageAtAmbientPoint f F x)
      (V : (D.toCompleteDevissageOver.stage
        (Fin.last D.toCompleteDevissageOver.last)).Y.left.Opens)
      (a : Γ((D.toCompleteDevissageOver.stage
        (Fin.last D.toCompleteDevissageOver.last)).Y.left, ⊤)),
      V = (D.toCompleteDevissageOver.stage
        (Fin.last D.toCompleteDevissageOver.last)).Y.left.basicOpen a →
      D.y (Fin.last D.toCompleteDevissageOver.last) ∈ V →
      ∃ W : D.StandardShrinking,
        W.model (Fin.last D.toCompleteDevissageOver.last) =
          V ⊓ ((D.toCompleteDevissageOver.stage
            (Fin.last D.toCompleteDevissageOver.last)).Y.hom ⁻¹ᵁ W.base))

/- Lemma 38.5.6 (3): every open neighbourhood of the distinguished source
point contains the source open of a standard shrinking. -/
@[stacks 05HM] #check
  (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking.existsSourceLE :
    ∀ {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
      [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
      (D : CompleteDevissageAtAmbientPoint f F x) (U : X.Opens), x ∈ U →
      ∃ W : D.StandardShrinking, W.source ≤ U)
