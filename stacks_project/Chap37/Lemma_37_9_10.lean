/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation.Etale
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

/- Lemma 37.9.10: perturbing the two horizontal morphisms in a commutative diagram of
first-order thickenings by maps related through the canonical étale differential and
conormal comparisons preserves the primed commutative square.
-/
@[stacks 04BY] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.perturbation_commSq_of_etale :
    ∀ (S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : AlgebraicGeometry.Scheme.{u})
      (i₁ : T₁ ⟶ T₁') (j₁ : X₁ ⟶ X₁') (a₁ : T₁ ⟶ X₁)
      (a₁' : T₁' ⟶ X₁') (i₂ : T₂ ⟶ T₂') (j₂ : X₂ ⟶ X₂')
      (a₂ : T₂ ⟶ X₂) (a₂' : T₂' ⟶ X₂')
      (h : T₂ ⟶ T₁) (h' : T₂' ⟶ T₁')
      (f : X₂ ⟶ X₁) (f' : X₂' ⟶ X₁') (s : S₂ ⟶ S₁)
      [T₁.Over S₁] [T₁'.Over S₁] [X₁.Over S₁] [X₁'.Over S₁]
      [T₂.Over S₂] [T₂'.Over S₂] [X₂.Over S₂] [X₂'.Over S₂]
      [i₁.IsOver S₁] [j₁.IsOver S₁] [a₁.IsOver S₁] [a₁'.IsOver S₁]
      [i₂.IsOver S₂] [j₂.IsOver S₂] [a₂.IsOver S₂] [a₂'.IsOver S₂]
      [AlgebraicGeometry.IsFirstOrderThickening i₁]
      [AlgebraicGeometry.IsFirstOrderThickening j₁]
      [AlgebraicGeometry.IsFirstOrderThickening i₂]
      [AlgebraicGeometry.IsFirstOrderThickening j₂]
      [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale s]
      (sqA₁ : CommSq a₁ i₁ j₁ a₁') (sqA₂ : CommSq a₂ i₂ j₂ a₂')
      (sqT : CommSq h i₂ i₁ h') (sqX : CommSq f j₂ j₁ f')
      (sq₀ : CommSq a₂ h f a₁) (sq₁ : CommSq a₂' h' f' a₁')
      (sqS : CommSq f' (X₂' ↘ S₂) (X₁' ↘ S₁) s)
      (theta₁ : (AlgebraicGeometry.Scheme.Modules.pullback a₁).obj
        Ω[(X₁ ↘ S₁).toShHom] ⟶ AlgebraicGeometry.Scheme.Hom.conormalSheaf i₁)
      (b₁' : T₁' ⟶ X₁') (b₂' : T₂' ⟶ X₂')
      (hb₁ : AlgebraicGeometry.Scheme.Hom.Deformation.IsPerturbation
        S₁ i₁ j₁ a₁ a₁' sqA₁ theta₁ b₁')
      (hb₂ : AlgebraicGeometry.Scheme.Hom.Deformation.IsPerturbation
        S₂ i₂ j₂ a₂ a₂' sqA₂
          (AlgebraicGeometry.Scheme.Hom.Deformation.pullbackPerturbationMap
            s f h a₁ a₂ i₁ i₂ h'
            (AlgebraicGeometry.Scheme.Hom.Deformation.baseCommSq
              s j₁ j₂ f f' sqX sqS)
            sq₀ sqT theta₁) b₂'),
      CommSq b₂' h' f' b₁')
