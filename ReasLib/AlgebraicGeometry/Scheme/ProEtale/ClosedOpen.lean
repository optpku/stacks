/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (F : Sheaf (topology X) AddCommGrpCat.{u + 1})

/-- The adjunction counit `j_! (j⁻¹ F) ⟶ F` for the open complement inclusion
`j = (closedImmersionComplement i).ι`, with `j_! = abelianExtensionByZero` and
`j⁻¹ = restrictionSheaf` on the small pro-étale site. -/
def abelianClosedOpenCounit :
    (abelianExtensionByZero.{u, u + 1} (closedImmersionComplement i).ι).obj
      ((restrictionSheaf (closedImmersionComplement i).ι AddCommGrpCat.{u + 1}).obj F) ⟶
        F :=
  (abelianExtensionByZero_adjunction.{u, u + 1}
    (closedImmersionComplement i).ι).counit.app F

/-- The adjunction unit `F ⟶ i_* (i⁻¹ F)` of small pro-étale inverse image and
direct image along a closed immersion, with `i_* = smallPushforward` and
`i⁻¹ = smallInverseImage`. -/
def abelianClosedOpenUnit :
    F ⟶ (smallPushforward i).obj ((smallInverseImage i).obj F) :=
  ((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (topology X) (topology Z)).unit.app F

/-- The open-complement counit followed by the closed-immersion unit is zero. -/
theorem abelianClosedOpen_comp_zero :
    abelianClosedOpenCounit i F ≫ abelianClosedOpenUnit i F = 0 := sorry

/-- The canonical complementary closed/open short complex
`j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F` of abelian sheaves on the small pro-étale site. -/
def abelianClosedOpenShortComplex :
    ShortComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) where
  f := abelianClosedOpenCounit i F
  g := abelianClosedOpenUnit i F
  zero := abelianClosedOpen_comp_zero i F

/-- The first map of the closed/open short complex is the extension-by-zero counit. -/
theorem abelianClosedOpenShortComplex_f :
    (abelianClosedOpenShortComplex i F).f = abelianClosedOpenCounit i F := rfl

/-- The second map of the closed/open short complex is the closed-immersion unit. -/
theorem abelianClosedOpenShortComplex_g :
    (abelianClosedOpenShortComplex i F).g = abelianClosedOpenUnit i F := rfl

/-- For a closed immersion with quasi-compact open complement, every abelian
pro-étale sheaf has the canonical short exact sequence
`0 ⟶ j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F ⟶ 0`. -/
theorem abelianClosedOpenShortComplex_shortExact
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact (closedImmersionComplement i).ι]
    (F : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    (abelianClosedOpenShortComplex i F).ShortExact := sorry

end AlgebraicGeometry.Scheme.ProEt
