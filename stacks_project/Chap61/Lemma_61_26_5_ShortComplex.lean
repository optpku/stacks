module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import stacks_project.Chap61.Definition_61_26_1_ExtensionByZero
public import stacks_project.Chap61.Lemma_61_17_2_Pushforward
public import stacks_project.Chap61.Lemma_61_17_3_Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable [∀ F : (closedImmersionComplement i).toScheme.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (restriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (smallProetalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
variable [HasZeroMorphisms (Sheaf (topology X) AddCommGrpCat.{u + 1})]
variable (F : Sheaf (topology X) AddCommGrpCat.{u + 1})

/-- The adjunction counit `j_! (j⁻¹ F) ⟶ F` for the open complement inclusion
`j = (closedImmersionComplement i).ι`, with `j_! = abelianExtensionByZero` and
`j⁻¹ = restrictionSheaf` on `ProEt.topology`. -/
def abelianClosedOpenCounit :
    (abelianExtensionByZero (closedImmersionComplement i).ι).obj
      ((restrictionSheaf (closedImmersionComplement i).ι AddCommGrpCat.{u + 1}).obj F) ⟶
        F :=
  (abelianExtensionByZero_adjunction (closedImmersionComplement i).ι).counit.app F

/-- The adjunction unit `F ⟶ i_* (i⁻¹ F)` of small pro-étale inverse image and
direct image along a closed immersion, with `i_* = smallPushforward` and
`i⁻¹ = smallInverseImage`. -/
def abelianClosedOpenUnit :
    F ⟶ (smallPushforward i).obj ((smallInverseImage i).obj F) :=
  ((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (topology X) (topology Z)).unit.app F

/-- The two complementary maps compose to zero. -/
theorem abelianClosedOpen_comp_zero :
    abelianClosedOpenCounit i F ≫ abelianClosedOpenUnit i F = 0 := sorry

/-- The underived complementary closed/open short complex
`j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F` of abelian sheaves on `X_proétale`. -/
def abelianClosedOpenShortComplex :
    ShortComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) where
  f := abelianClosedOpenCounit i F
  g := abelianClosedOpenUnit i F
  zero := abelianClosedOpen_comp_zero i F

/-- The first map of `abelianClosedOpenShortComplex` is the extension-by-zero
counit. -/
theorem abelianClosedOpenShortComplex_f :
    (abelianClosedOpenShortComplex i F).f = abelianClosedOpenCounit i F := sorry

/-- The second map of `abelianClosedOpenShortComplex` is the closed-immersion
direct-image unit. -/
theorem abelianClosedOpenShortComplex_g :
    (abelianClosedOpenShortComplex i F).g = abelianClosedOpenUnit i F := sorry

end AlgebraicGeometry.Scheme.ProEt
