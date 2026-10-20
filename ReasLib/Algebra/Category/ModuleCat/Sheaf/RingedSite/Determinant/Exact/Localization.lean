/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local formulas for determinant morphisms of split short exact sequences

The determinant comparison associated to a splitting can be formed after restricting a short
complex to a slice site, without first identifying a restricted determinant with the determinant
of the restricted module.  Its source is the restriction of the global tensor product of the two
determinants, and its target is the restriction of the global exterior algebra of the middle term.
This is the ambient, rank-free localization API needed for comparing locally chosen splittings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant.Exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {S : ShortComplex (ringedSiteModuleCategory J O)}

/-- The ambient determinant morphism attached to a splitting after restriction to `C / U`.
It is defined over the restrictions of the global determinant sheaves, so it does not require a
rank hypothesis or a comparison between restriction and the determinant kernel construction. -/
@[stacks 0B38 "ambient split determinant morphism after localized restriction"]
noncomputable def splitAmbientHom
    (s : (S.map (Localization.restriction O U)).Splitting) :
    (tensorObj (sheaf S.X₁) (sheaf S.X₃)).over U ⟶
      (ExteriorAlgebra.sheaf O S.X₂).over U :=
  @Functor.OplaxMonoidal.δ _ _ _ _ _ _ (Localization.restriction O U)
      (Localization.restrictionMonoidal O U).toOplaxMonoidal
      (sheaf S.X₁) (sheaf S.X₃) ≫
    tensorHom
      (SheafOfModules.Hom.over (ι S.X₁) U)
      (SheafOfModules.Hom.over (ι S.X₃) U) ≫
    tensorHom
      (ExteriorAlgebra.overIso O U S.X₁).hom
      (ExteriorAlgebra.overIso O U S.X₃).hom ≫
    tensorHom
      (ExteriorAlgebra.map (O.over U) ((Localization.restriction O U).map S.f))
      (ExteriorAlgebra.map (O.over U) s.s) ≫
    ExteriorAlgebra.mul (O.over U) (S.X₂.over U) ≫
    (ExteriorAlgebra.overIso O U S.X₂).inv

namespace SplitAmbientHom

/-- After the target exterior-algebra localization comparison, the restricted ambient
determinant morphism is the local formula written with the restrictions of the two global
determinant inclusions. -/
@[reassoc, stacks 0B38 "localized ambient split determinant formula"]
theorem overIso_hom
    (s : (S.map (Localization.restriction O U)).Splitting) :
    splitAmbientHom O U s ≫ (ExteriorAlgebra.overIso O U S.X₂).hom =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ (Localization.restriction O U)
          (Localization.restrictionMonoidal O U).toOplaxMonoidal
          (sheaf S.X₁) (sheaf S.X₃) ≫
        tensorHom
          (SheafOfModules.Hom.over (ι S.X₁) U)
          (SheafOfModules.Hom.over (ι S.X₃) U) ≫
        tensorHom
          (ExteriorAlgebra.overIso O U S.X₁).hom
          (ExteriorAlgebra.overIso O U S.X₃).hom ≫
        tensorHom
          (ExteriorAlgebra.map (O.over U) ((Localization.restriction O U).map S.f))
          (ExteriorAlgebra.map (O.over U) s.s) ≫
        ExteriorAlgebra.mul (O.over U) (S.X₂.over U) := sorry

/-- The restricted ambient determinant morphism is independent of the splitting chosen on the
restricted short complex. -/
@[stacks 0B38 "independence of localized ambient determinant morphisms"]
theorem independent
    (s t : (S.map (Localization.restriction O U)).Splitting) :
    splitAmbientHom O U s = splitAmbientHom O U t := sorry

/-- Local ambient determinant morphisms attached to splittings on two objects agree after
restriction to any common refinement. -/
@[stacks 0B38 "overlap compatibility of localized ambient determinant morphisms"]
theorem restrict_eq
    {V Z : C}
    [HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (a : Z ⟶ U) (b : Z ⟶ V)
    (s : (S.map (Localization.restriction O U)).Splitting)
    (t : (S.map (Localization.restriction O V)).Splitting) :
    InternalHom.restrictFun O
        (tensorObj (sheaf S.X₁) (sheaf S.X₃))
        (ExteriorAlgebra.sheaf O S.X₂) a.op (splitAmbientHom O U s) =
      InternalHom.restrictFun O
        (tensorObj (sheaf S.X₁) (sheaf S.X₃))
        (ExteriorAlgebra.sheaf O S.X₂) b.op (splitAmbientHom O V t) := sorry

/-- Restricting the global ambient formula attached to a splitting agrees with the ambient
formula attached to the induced splitting of the restricted short complex. -/
@[stacks 0B38 "restriction naturality of the ambient split determinant morphism"]
theorem mapSplitting (s : S.Splitting) :
    splitAmbientHom O U (s.map (Localization.restriction O U)) =
      SheafOfModules.Hom.over (splitHom O s ≫ ι S.X₂) U := sorry

/-- Any splitting on the restricted short complex yields the restriction of the global split
determinant morphism, after composing with the restricted determinant inclusion. -/
@[stacks 0B38 "localized ambient morphism and the global split determinant morphism"]
theorem eq_over_comp_ι
    (s : (S.map (Localization.restriction O U)).Splitting) (t : S.Splitting) :
    splitAmbientHom O U s =
      SheafOfModules.Hom.over (splitHom O t) U ≫
        SheafOfModules.Hom.over (ι S.X₂) U := sorry

end SplitAmbientHom

end SheafOfModules.RingedSite.Determinant.Exact
