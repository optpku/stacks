/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Inverse image ⊣ pushforward on small étale sheaves of algebraic spaces

The adjunction `f_small^{-1} ⊣ f_small,*` is the composite of the cocontinuous
adjunction along `smallEtaleInclusion` and the continuous adjunction along
`etaleBaseChange`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of `A`-valued sheaves is left adjoint to small étale pushforward,
as the composite of the Kan-extension adjunction along `etaleBaseChange` and the
cocontinuous adjunction along `smallEtaleInclusion`. -/
def sheafAdjunction (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafInverseImage A f ⊣ sheafPushforward A f :=
  (sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
      (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
    ((smallEtaleInclusion X).sheafAdjunctionCocontinuous A
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `sheafAdjunction` is the composite of the continuous pullback adjunction along
`etaleBaseChange` with the cocontinuous adjunction along `smallEtaleInclusion`. -/
theorem sheafAdjunction_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A] :
    sheafAdjunction A f =
      (sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
          (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
        ((smallEtaleInclusion X).sheafAdjunctionCocontinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)) :=
  rfl

/-- The counit of `sheafAdjunction` is the composite of the two site-level counits. -/
theorem sheafAdjunction_counit_eq (A : Type v) [Category.{w} A] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A]
    (G : Sheaf (smallEtaleTopology X) A) :
    (sheafAdjunction A f).counit.app G =
      ((smallEtaleInclusion X).sheafPushforwardContinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)).map
        ((sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) A
            (smallEtaleTopology Y) (spacesEtaleTopology X)).counit.app
          (((smallEtaleInclusion X).sheafPushforwardCocontinuous A
              (smallEtaleTopology X) (spacesEtaleTopology X)).obj G)) ≫
        ((smallEtaleInclusion X).sheafAdjunctionCocontinuous A
          (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
