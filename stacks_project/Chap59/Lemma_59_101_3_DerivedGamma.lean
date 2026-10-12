/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import Mathlib.Algebra.Homology.QuasiIso
public import stacks_project.Chap59.Lemma_59_101_3_TensorComplex

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Quasi-isomorphisms of cochain complexes of affine-fppf abelian sheaves. -/
abbrev fppfAffineAbelianSheafQuasiIso (A : CommRingCat.{u})
    [Preadditive (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})] :
    MorphismProperty
      (CochainComplex (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) ℤ) :=
  HomologicalComplex.quasiIso
    (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) (up ℤ)

/-- Unfolding of affine-fppf sheaf cochain quasi-isomorphisms. -/
theorem fppfAffineAbelianSheafQuasiIso_eq (A : CommRingCat.{u})
    [Preadditive (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})] :
    fppfAffineAbelianSheafQuasiIso A =
      HomologicalComplex.quasiIso
        (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) (up ℤ) :=
  sorry

/-- Affine-fppf global sections admit a cochain-level total right derived functor. -/
instance hasRightDerived_fppfAffineAbelianGamma (A : CommRingCat.{u})
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Abelian (fppfAffineAbelianSheaf A)]
    [(Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).Additive]
    [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    (RightDerived.Cochain.toDerived
        (Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso
        (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}) (up ℤ)) :=
  sorry

/-- Affine-fppf derived global sections of abelian sheaves. -/
abbrev fppfAffineAbelianDerivedGamma (A : CommRingCat.{u})
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Abelian (fppfAffineAbelianSheaf A)]
    [(Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).Additive]
    [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory AddCommGrpCat.{u}] :=
  RightDerived.Cochain.functor
    (Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})

/-- Degreewise unit `M^n ⟶ Γ(F^n)` of the affine-fppf sheafification. -/
noncomputable def tensorExtensionComplex_fppfAffine_toGamma_f (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) (n : ℤ)
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Preadditive (fppfAffineAbelianSheaf A)]
    [(presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj (M.X n)) ⟶
      (Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).obj
        ((fppfAffineTensorExtensionAbelianSheafComplex A M).X n) :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
      ((ModuleCat.extendRestrictScalarsAdj
          ((affineOverSpecToUnder A).obj (op (affineOverSpecId A))).hom.hom).unit.app (M.X n)) ≫
    eqToHom rfl ≫
    ((sheafificationAdjunction (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).unit.app
        ((fppfAffineTensorExtensionAbelianPresheafComplex A M).X n)).app
      (op (affineOverSpecId A)) ≫
    (Sheaf.ΓNatIsoSheafSections (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}
        (isTerminal_affineOverSpecId A)).inv.app
      ((fppfAffineTensorExtensionAbelianSheafComplex A M).X n)

/-- The canonical cochain map `M ⟶ Γ((Aff / Spec A)_fppf, F)`. -/
noncomputable def tensorExtensionComplex_fppfAffine_toGamma (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ))
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [Preadditive (fppfAffineAbelianSheaf A)]
    [(presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).PreservesZeroMorphisms] :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj M ⟶
      ((Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).mapHomologicalComplex
          (up ℤ)).obj
        (fppfAffineTensorExtensionAbelianSheafComplex A M) where
  f n := tensorExtensionComplex_fppfAffine_toGamma_f A M n
  comm' := sorry

/-- The canonical derived comparison `M ⟶ RΓ((Aff / Spec A)_fppf, F)`. -/
noncomputable def tensorExtensionComplex_fppfAffine_toDerivedGamma (A : CommRingCat.{u})
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ))
    [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
    [(presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).PreservesZeroMorphisms]
    [Abelian (fppfAffineAbelianSheaf A)]
    [(Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).Additive]
    [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    (DerivedCategory.Q :
        CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u}).obj
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj M) ⟶
      (fppfAffineAbelianDerivedGamma A).obj
        (DerivedCategory.Q.obj (fppfAffineTensorExtensionAbelianSheafComplex A M)) :=
  DerivedCategory.Q.map (tensorExtensionComplex_fppfAffine_toGamma A M) ≫
    (RightDerived.Cochain.unit
        (Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})).app
      (fppfAffineTensorExtensionAbelianSheafComplex A M)

end AlgebraicGeometry.Scheme.AssociatedModule
