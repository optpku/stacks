/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.Homotopy
public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.AdicCompletion
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

universe u

namespace CosimplicialModule.Homotopic

variable {A : CosimplicialObject CommRingCat.{u}}

/-- Tensoring with the identity of a cosimplicial module preserves linear homotopy. -/
theorem tensor {K M L : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ ψ : K ⟶ M) (h : CosimplicialModule.Homotopic φ ψ) :
    CosimplicialModule.Homotopic (Monoidal.tensorHom φ (𝟙 L))
      (Monoidal.tensorHom ψ (𝟙 L)) := sorry

/-- Exterior powers preserve linear homotopy of cosimplicial module morphisms. -/
theorem exteriorPower {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ ψ : K ⟶ M) (i : ℕ) (h : CosimplicialModule.Homotopic φ ψ) :
    CosimplicialModule.Homotopic (ExteriorPower.hom (cosimplicialCommRing A) φ i)
      (ExteriorPower.hom (cosimplicialCommRing A) ψ i) := sorry

/-- Extension of scalars along a cosimplicial ring morphism preserves linear homotopy
as a relation on morphisms over the target ring. -/
theorem extendScalars {B : CosimplicialObject CommRingCat.{u}}
    {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (φ ψ : K ⟶ M)
    (f : A ⟶ B) (h : CosimplicialModule.Homotopic φ ψ) :
    CosimplicialModule.Homotopic (extendScalarsHom f φ) (extendScalarsHom f ψ) := sorry

/-- Degreewise ideal-adic completion preserves linear homotopy of module morphisms. -/
theorem adicCompletion {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ ψ : K ⟶ M) (I : CosimplicialIdeal A) (h : CosimplicialModule.Homotopic φ ψ) :
    CosimplicialModule.Homotopic (CosimplicialModule.adicCompletionMap I φ)
      (CosimplicialModule.adicCompletionMap I ψ) := sorry

/-- Symmetric powers preserve linear homotopy of cosimplicial module morphisms. -/
theorem symmetricPower {K M : PresheafOfModules.{u} (moduleRingPresheaf A)}
    (φ ψ : K ⟶ M) (i : ℕ) (h : CosimplicialModule.Homotopic φ ψ) :
    CosimplicialModule.Homotopic (SymmetricPower.hom (cosimplicialCommRing A) φ i)
      (SymmetricPower.hom (cosimplicialCommRing A) ψ i) := sorry

end CosimplicialModule.Homotopic
