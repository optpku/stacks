/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap59.Lemma_59_101_3_AffineOverUnder
public import stacks_project.Chap59.Lemma_59_101_3_Instances

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ModuleValuedFunctor
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The complex of presheaves of `𝒪`-modules on `(Aff / Spec A)_fppf` given by
`Spec B / Spec A ↦ M^n ⊗[A] B`. -/
noncomputable def fppfAffineTensorExtensionComplex (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) :
    HomologicalComplex (bundled.{u, u} A) (up ℤ) :=
  ((tensorExtensionFunctor A).mapHomologicalComplex (up ℤ)).obj M

/-- Evaluating the tensor-extension complex at an `A`-algebra `B` recovers
extension of scalars of the corresponding term of `M`. -/
theorem fppfAffineTensorExtensionComplex_obj (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) (n : ℤ) (B : Under A) :
    ((fppfAffineTensorExtensionComplex A M).X n).obj B =
      (ModuleCat.extendScalars B.hom.hom).obj (M.X n) :=
  tensorExtensionFunctor_obj_obj A (M.X n) B

/-- The cochain complex of abelian presheaves on `(Aff / Spec A)_fppf`. -/
noncomputable def fppfAffineTensorExtensionAbelianPresheafComplex (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) :
    HomologicalComplex ((Spec A).AffineOverᵒᵖ ⥤ AddCommGrpCat.{u}) (up ℤ) :=
  (((whiskeringLeft (Spec A).AffineOverᵒᵖ (Under A) AddCommGrpCat.{u}).obj
        (affineOverSpecToUnder A)).mapHomologicalComplex (up ℤ)).obj
    (((ModuleValuedFunctor.forget A).mapHomologicalComplex (up ℤ)).obj
      (fppfAffineTensorExtensionComplex A M))

/-- Sheafification of the abelian presheaf complex on the affine fppf topology. -/
noncomputable def fppfAffineTensorExtensionAbelianSheafComplex (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ))
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Preadditive (fppfAffineAbelianSheaf A)]
    [(presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    CochainComplex (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) ℤ :=
  ((presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).mapHomologicalComplex
      (up ℤ)).obj
    (fppfAffineTensorExtensionAbelianPresheafComplex A M)

end AlgebraicGeometry.Scheme.AssociatedModule
