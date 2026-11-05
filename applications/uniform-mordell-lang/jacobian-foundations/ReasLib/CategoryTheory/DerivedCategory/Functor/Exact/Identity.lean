module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Exactness.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity exact functors on derived categories

The derived functor of the bundled exact identity is canonically naturally
isomorphic to the identity of the derived category.  The comparison is
constructed from localization liftings and does not choose representatives.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- The identity map on cochain complexes followed by localization is
canonically the localization functor. -/
@[stacks 015F "factorization for the exact derived identity"]
noncomputable def idFactors :
    (ExactFunctor.id A).obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ≅
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (up ℤ))
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ≪≫
    Functor.leftUnitor
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)

/-- Passage to the derived category sends the bundled exact identity to the
identity functor, up to its canonical localization comparison. -/
@[stacks 015F "passage to derived categories preserves the exact identity"]
noncomputable def idFunctorIso :
    (ExactFunctor.id A).mapDerivedCategory ≅
      Functor.id (DerivedCategory A) :=
  Localization.liftNatIso
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))
    ((ExactFunctor.id A).obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A))
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (ExactFunctor.id A).mapDerivedCategory
    (Functor.id (DerivedCategory A))
    (idFactors A)

/-- The objectwise identity comparison for the derived functor of the
bundled exact identity. -/
noncomputable abbrev idObjIso (K : DerivedCategory A) :
    (ExactFunctor.id A).mapDerivedCategory.obj K ≅ K :=
  (idFunctorIso A).app K

/-- Computation of the forward identity comparison on an object in the image
of the localization functor. -/
theorem idFunctorIso_hom_app_Q (K : CochainComplex A ℤ) :
    (idFunctorIso A).hom.app (DerivedCategory.Q.obj K) =
      (ExactFunctor.id A).obj.mapDerivedCategoryFactors.hom.app K ≫
        (idFactors A).hom.app K := sorry

/-- Computation of the inverse identity comparison on an object in the image
of the localization functor. -/
theorem idFunctorIso_inv_app_Q (K : CochainComplex A ℤ) :
    (idFunctorIso A).inv.app (DerivedCategory.Q.obj K) =
      (idFactors A).inv.app K ≫
        (ExactFunctor.id A).obj.mapDerivedCategoryFactors.inv.app K := sorry

/-- Forward naturality of the objectwise exact-derived identity comparison. -/
@[reassoc]
theorem idObjIso_hom_naturality {K L : DerivedCategory A} (f : K ⟶ L) :
    (ExactFunctor.id A).mapDerivedCategory.map f ≫ (idObjIso A L).hom =
      (idObjIso A K).hom ≫ f := sorry

/-- Inverse naturality of the objectwise exact-derived identity comparison. -/
@[reassoc]
theorem idObjIso_inv_naturality {K L : DerivedCategory A} (f : K ⟶ L) :
    f ≫ (idObjIso A L).inv =
      (idObjIso A K).inv ≫
        (ExactFunctor.id A).mapDerivedCategory.map f := sorry

namespace idFunctorIso

/-- The components of `idFunctorIso` are the objectwise identity
comparisons. -/
@[simp]
theorem app (K : DerivedCategory A) :
    (idFunctorIso A).app K = idObjIso A K := sorry

end idFunctorIso

end CategoryTheory.ExactFunctor.MapDerivedCategory
