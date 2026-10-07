module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Abelian
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap59.Lemma_59_101_3_AffineOverUnder

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ModuleValuedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The category of module-valued functors has componentwise zero morphisms. -/
noncomputable instance bundled_hasZeroMorphisms (A : CommRingCat.{u}) :
    HasZeroMorphisms (bundled.{u, u} A) :=
  bundledHasZeroMorphisms A

/-- Tensor extension preserves zero morphisms. -/
instance tensorExtensionFunctor_preservesZeroMorphisms (A : CommRingCat.{u}) :
    (tensorExtensionFunctor A).PreservesZeroMorphisms := sorry

/-- Forgetting module structure on module-valued functors preserves zero morphisms. -/
instance forget_preservesZeroMorphisms (A : CommRingCat.{u}) :
    (ModuleValuedFunctor.forget A).PreservesZeroMorphisms := sorry

/-- Precomposition with `affineOverSpecToUnder` preserves zero morphisms. -/
instance affineOverSpecToUnder_whisker_preservesZeroMorphisms (A : CommRingCat.{u}) :
    ((whiskeringLeft (Spec A).AffineOverᵒᵖ (Under A) AddCommGrpCat.{u}).obj
      (affineOverSpecToUnder A)).PreservesZeroMorphisms := sorry

/-- Abelian sheaves on the affine fppf site of `Spec A`. -/
abbrev fppfAffineAbelianSheaf (A : CommRingCat.{u}) :=
  Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}

/-- Preadditive structure on affine-fppf abelian sheaves along the derived-category path. -/
instance (priority := 1000) instPreadditive_fppfAffineAbelianSheaf_derived
    (A : CommRingCat.{u}) [Abelian (fppfAffineAbelianSheaf A)] :
    Preadditive (fppfAffineAbelianSheaf A) :=
  Abelian.toPreadditive

/-- Zero morphisms on affine-fppf abelian sheaves along the derived-category path. -/
abbrev fppfAffineAbelianSheafHasZeroMorphisms (A : CommRingCat.{u})
    [Preadditive (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})] :
    HasZeroMorphisms (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) :=
  Preadditive.preadditiveHasZeroMorphisms

attribute [instance 10000] fppfAffineAbelianSheafHasZeroMorphisms

/-- Unfolding of the affine-fppf sheaf zero-morphism instance. -/
theorem fppfAffineAbelianSheafHasZeroMorphisms_eq (A : CommRingCat.{u})
    [Preadditive (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})] :
    fppfAffineAbelianSheafHasZeroMorphisms A =
      Preadditive.preadditiveHasZeroMorphisms :=
  sorry

/-- Global sections of abelian sheaves on the affine fppf site are additive. -/
instance fppfAffine_globalSections_additive (A : CommRingCat.{u})
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Preadditive (fppfAffineAbelianSheaf A)] :
    (Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).Additive :=
  sorry

end AlgebraicGeometry.Scheme.AssociatedModule
