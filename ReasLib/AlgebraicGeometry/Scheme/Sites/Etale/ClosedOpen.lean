/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The extension-by-zero counit for the open complement of a closed immersion. -/
def closedOpenCounit :
    (abelianExtensionByZero (closedImmersionComplement i).ι).obj
      ((etaleRestrictionSheaf (closedImmersionComplement i).ι AddCommGrpCat.{u}).obj F) ⟶ F :=
  (abelianExtensionByZeroAdjunction (closedImmersionComplement i).ι).counit.app F

/-- The inverse-image/direct-image unit for a closed immersion on abelian étale sheaves. -/
def closedOpenUnit :
    F ⟶ ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology).obj ((abelianInverseImage i).obj F) :=
  (abelianAdjunctionDirectImage i).unit.app F

/-- The open-complement counit followed by the closed-immersion unit is zero. -/
theorem closedOpen_comp_zero :
    closedOpenCounit i F ≫ closedOpenUnit i F = 0 := sorry

/-- The canonical closed/open short complex of abelian étale sheaves
`j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F`, where `j` is the open complement of `i`. -/
def closedOpenShortComplex :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) where
  f := closedOpenCounit i F
  g := closedOpenUnit i F
  zero := closedOpen_comp_zero i F

/-- The first arrow of the closed/open short complex is the extension-by-zero counit. -/
theorem closedOpenShortComplex_f :
    (closedOpenShortComplex i F).f = closedOpenCounit i F := sorry

/-- The second arrow of the closed/open short complex is the inverse-image/direct-image unit. -/
theorem closedOpenShortComplex_g :
    (closedOpenShortComplex i F).g = closedOpenUnit i F := sorry

/-- Every abelian étale sheaf has a short exact closed/open sequence
`0 ⟶ j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F ⟶ 0`. -/
theorem closedOpenShortComplex_shortExact :
    (closedOpenShortComplex i F).ShortExact := sorry

end AlgebraicGeometry.Scheme.Etale
