/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineFppf
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineFppf

variable (A : CommRingCat.{u})
variable [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]

/-- The degreewise comparison to global sections is the composite of the extension-of-scalars
unit and the sheafification unit evaluated at the identity affine scheme. -/
def toGammaApp (M : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ) :
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj (M.X degree) ⟶
      (globalSections A).obj ((tensorSheafComplex A M).X degree) :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
      ((ModuleCat.extendRestrictScalarsAdj
        ((AffineOver.toUnder A).obj (op (AffineOver.specId A))).hom.hom).unit.app
        (M.X degree)) ≫
    eqToHom rfl ≫
    ((sheafificationAdjunction (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).unit.app
      ((tensorPresheafComplex A M).X degree)).app (op (AffineOver.specId A))

/-- The degreewise comparison to global sections commutes with the differentials. -/
theorem toGamma_comm (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (sourceDegree targetDegree : ℤ) (h : (up ℤ).Rel sourceDegree targetDegree) :
    toGammaApp A M sourceDegree ≫
        (((globalSections A).mapHomologicalComplex (up ℤ)).obj (tensorSheafComplex A M)).d
          sourceDegree targetDegree =
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj M).d
        sourceDegree targetDegree ≫ toGammaApp A M targetDegree := sorry

/-- The canonical cochain comparison from a module complex to affine-fppf global sections
of its tensor sheaf complex. -/
def toGamma (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj M ⟶
      ((globalSections A).mapHomologicalComplex (up ℤ)).obj (tensorSheafComplex A M) where
  f := toGammaApp A M
  comm' := toGamma_comm A M

variable [HasDerivedCategory (AbelianSheaf A)] [HasDerivedCategory AddCommGrpCat.{u}]

/-- The canonical derived comparison is localization of the cochain comparison followed
by the total-right-derived unit. -/
def toDerivedGamma (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (RF : DerivedCategory (AbelianSheaf A) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : RightDerived.Cochain.toDerived (globalSections A) ⟶ DerivedCategory.Q ⋙ RF) :
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u} ℤ ⥤
      DerivedCategory AddCommGrpCat.{u}).obj
        (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj M) ⟶
      RF.obj (DerivedCategory.Q.obj (tensorSheafComplex A M)) :=
  DerivedCategory.Q.map (toGamma A M) ≫
    α.app (tensorSheafComplex A M)

/-- Every module complex is identified with the derived affine-fppf global sections of
its tensor sheaf complex by the canonical comparison. -/
instance isIso_toDerivedGamma (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (RF : DerivedCategory (AbelianSheaf A) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : RightDerived.Cochain.toDerived (globalSections A) ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso (AbelianSheaf A) (up ℤ))] :
    IsIso (toDerivedGamma A M RF α) := sorry

end AlgebraicGeometry.Scheme.AffineFppf
