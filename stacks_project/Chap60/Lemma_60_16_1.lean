/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Homotopy.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory PresheafOfModules

universe u

/- Lemma 60.16.1 (1): tensoring with the identity preserves linear homotopy. -/
@[stacks 07KQ] #check (CosimplicialModule.Homotopic.tensor :
  ∀ {A : CosimplicialObject CommRingCat.{u}}
    {K M L : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M),
    CosimplicialModule.Homotopic φ ψ →
      CosimplicialModule.Homotopic (Monoidal.tensorHom φ (𝟙 L))
        (Monoidal.tensorHom ψ (𝟙 L)))

/- Lemma 60.16.1 (2): exterior powers preserve linear homotopy. -/
@[stacks 07KQ] #check (CosimplicialModule.Homotopic.exteriorPower :
  ∀ {A : CosimplicialObject CommRingCat.{u}}
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M) (i : ℕ),
    CosimplicialModule.Homotopic φ ψ →
      CosimplicialModule.Homotopic (ExteriorPower.hom (cosimplicialCommRing A) φ i)
        (ExteriorPower.hom (cosimplicialCommRing A) ψ i))

/- Lemma 60.16.1 (3): scalar extension preserves linear homotopy over the target ring. -/
@[stacks 07KQ] #check (CosimplicialModule.Homotopic.extendScalars :
  ∀ {A B : CosimplicialObject CommRingCat.{u}}
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M) (f : A ⟶ B),
    CosimplicialModule.Homotopic φ ψ →
      CosimplicialModule.Homotopic (extendScalarsHom f φ) (extendScalarsHom f ψ))

/- Lemma 60.16.1 (4): ideal-adic completion preserves linear homotopy. -/
@[stacks 07KQ] #check (CosimplicialModule.Homotopic.adicCompletion :
  ∀ {A : CosimplicialObject CommRingCat.{u}}
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M)
    (I : CosimplicialIdeal A), CosimplicialModule.Homotopic φ ψ →
      CosimplicialModule.Homotopic (CosimplicialModule.adicCompletionMap I φ)
        (CosimplicialModule.adicCompletionMap I ψ))

/- Lemma 60.16.1 (5): symmetric powers preserve linear homotopy. -/
@[stacks 07KQ] #check (CosimplicialModule.Homotopic.symmetricPower :
  ∀ {A : CosimplicialObject CommRingCat.{u}}
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M) (i : ℕ),
    CosimplicialModule.Homotopic φ ψ →
      CosimplicialModule.Homotopic (SymmetricPower.hom (cosimplicialCommRing A) φ i)
        (SymmetricPower.hom (cosimplicialCommRing A) ψ i))
