/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver.Spec
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorComplex
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineFppf

/-- Abelian-group-valued sheaves on the affine fppf site over `Spec A`. -/
abbrev AbelianSheaf (A : CommRingCat.{u}) :=
  Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}

/-- Evaluation at the identity affine scheme on the affine-fppf site. -/
abbrev globalSections (A : CommRingCat.{u}) : AbelianSheaf A ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj (op (AffineOver.specId A))

/-- The constant-sheaf adjunction for evaluation at the identity affine scheme. -/
def constantSheafGlobalSectionsAdj (A : CommRingCat.{u})
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}] :
    constantSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u} ⊣ globalSections A :=
  constantSheafAdj (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}
    (AffineOver.isTerminal_specId A)

/-- The affine-fppf tensor presheaf complex evaluates at an affine scheme with coordinate
`A`-algebra `B` to the underlying groups of the complex `B ⊗[A] M`. -/
def tensorPresheafComplex (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex ((Spec A).AffineOverᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  (((whiskeringLeft (Spec A).AffineOverᵒᵖ (Under A) AddCommGrpCat.{u}).obj
      (AffineOver.toUnder A)).mapHomologicalComplex (up ℤ)).obj
    (ModuleValuedFunctor.tensorComplex A M)

/-- Every term of the affine-fppf tensor presheaf complex is a sheaf. -/
theorem tensorPresheafComplex_isSheaf (A : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ) :
    Presheaf.IsSheaf (bigAffineFppfTopology (Spec A))
      ((tensorPresheafComplex A M).X degree) := sorry

/-- The sheaf complex obtained by sheafifying the affine-fppf tensor presheaf complex. -/
def tensorSheafComplex (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}] :
    CochainComplex (AbelianSheaf A) ℤ :=
  ((presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).mapHomologicalComplex
    (up ℤ)).obj (tensorPresheafComplex A M)

end AlgebraicGeometry.Scheme.AffineFppf
