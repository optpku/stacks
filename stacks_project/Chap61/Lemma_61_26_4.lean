/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (A : Type u₁) [Category.{v₁} A]

section ExtensionByZero

variable [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify (topology U) A] [HasWeakSheafify (topology X) A]
variable [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseLeftKanExtension F]
variable [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F]

/- Lemma 61.26.4: For an open immersion, extension by zero and direct image
restrict back to the identity, and both functors are fully faithful. -/
@[stacks 09BN] #check
  (AlgebraicGeometry.Scheme.ProEt.idIso_extensionByZero_comp_restrictionSheaf j A :
    Nonempty (𝟭 (Sheaf (topology U) A) ≅
      extensionByZero j A ⋙ restrictionSheaf j A))

#check (AlgebraicGeometry.Scheme.ProEt.extensionByZero_unit_isIso_of_isOpenImmersion j A :
  IsIso (extensionByZero_adjunction j A).unit)

#check (AlgebraicGeometry.Scheme.ProEt.extensionByZeroFullyFaithful_of_isOpenImmersion j A :
  Nonempty (extensionByZero j A).FullyFaithful)

end ExtensionByZero

section DirectImage

variable [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F]

#check (AlgebraicGeometry.Scheme.ProEt.directImage_comp_restrictionSheaf_isoId j A :
  Nonempty (directImage j A ⋙ restrictionSheaf j A ≅ 𝟭 (Sheaf (topology U) A)))

#check (AlgebraicGeometry.Scheme.ProEt.directImage_counit_isIso_of_isOpenImmersion j A :
  IsIso (directImage_adjunction j A).counit)

#check (AlgebraicGeometry.Scheme.ProEt.directImageFullyFaithful_of_isOpenImmersion j A :
  Nonempty (directImage j A).FullyFaithful)

end DirectImage

end ProEt

end AlgebraicGeometry.Scheme
