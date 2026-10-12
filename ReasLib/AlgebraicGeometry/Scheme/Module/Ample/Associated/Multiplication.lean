/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Associated.Multiplication
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Pullback coherence for associated twisted-section multiplication

The normalized comparison between pulled-back associated twisted-section sheaves and
quasicoherent modules respects the canonical multiplication by integral twists.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap

variable {X : Scheme.{u}}

/-- The normalized pullback comparison for associated twisted-section sheaves carries the
canonical multiplication morphism to the tensor product of its two comparison components. -/
theorem pullback_associatedTwisted_mul_comm
    (L : X.Modules) [Invertible L] [IsAmple L]
    (f : X ⟶ Proj (RingedSpace.GradedSections.grading L))
    (hf : IsSectionRingProjMap L f)
    (e :
      (ObjectProperty.ι (fun G : X.Modules ↦ G.IsQuasicoherent) ⋙
          GradedSections.associatedTwistedFunctor L ⋙ pullback f) ≅
        ObjectProperty.ι (fun G : X.Modules ↦ G.IsQuasicoherent))
    (h_e :
      ∀ (G : ObjectProperty.FullSubcategory
          (fun G : X.Modules ↦ G.IsQuasicoherent))
        (m : GradedSections.twistedInternalGrading L G.obj 0),
        ((globalSectionsPullback f
              (GradedSections.associatedTwistedSheaf L G.obj) ≫
            globalSectionsMap (e.hom.app G)).hom)
            (GradedSections.degreeZeroToAssociatedTwistedGlobalSections L G.obj m) =
          GradedSections.twistedDegreeZeroIso L G.obj m)
    (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ)
    (hLn : (L ^⊗ n).IsQuasicoherent)
    (hFLn : (F ⊗ L ^⊗ n).IsQuasicoherent)
    (C : GradedSections.AssociatedTwistedMultiplication L F) :
    pullbackTensorMap f (C.hom n) ≫
        e.hom.app ⟨F ⊗ L ^⊗ n, hFLn⟩ =
      e.hom.app ⟨F, hF⟩ ⊗ₘ e.hom.app ⟨L ^⊗ n, hLn⟩ := sorry

end AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap
