/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleDescent.Abelian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.CartesianDescent

/-!
# Abelian cartesian modules and exactness of their inclusion

Flatness of the two degree-one cofaces makes cartesian modules an abelian category.
It does not universally imply exactness of their inclusion into all module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped Simplicial
open RingedSite
open CategoryTheory.SimplicialSites
open CategoryTheory.SimplicialSites.Module

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

section OfIsFlatDelta01

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Finite products of cartesian `O`-modules remain cartesian, with no flatness hypothesis. -/
theorem instHasFiniteProductsCartesian : HasFiniteProducts (Cartesian C J O) :=
  sorry

variable [HasSheafify ((J ⦋0⦌).toGrothendieck) AddCommGrpCat.{w}]
variable [((J ⦋0⦌).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- If the two degree-one coface morphisms are flat, cartesian modules form an abelian category. -/
@[implicit_reducible]
def instAbelian_of_isFlat_delta01
    [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
    [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))] :
    Abelian (Cartesian C J O) :=
  @abelianOfEquivalence (Cartesian C J O) _ inferInstance
    (instHasFiniteProductsCartesian C J O) (FaceDescent C J O) _
    (instAbelianFaceDescent_of_isFlat_delta01 C J O)
    (cartesianEquivalence C J O).functor inferInstance

end OfIsFlatDelta01

/-- Flatness of the two degree-one cofaces does not universally imply exactness of
the inclusion of cartesian modules into all module sheaves. -/
theorem not_forall_exactInclusion_of_isFlat_delta01 [UnivLE.{max u v, w}] :
    ¬ ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
      [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
      [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
      [IsMorphismDiagram.{u, v, w} C J]
      (O : Sheaf (topology C J) RingCat.{w})
      [(topology C J).HasSheafCompose (forget RingCat.{w})]
      [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
      [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
      [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
        (ofStage C n).op.HasPointwiseRightKanExtension P]
      [∀ n, (SheafOfModules.restrictScalars.{w}
        (stageMorphism C J O n).structureMap).IsRightAdjoint]
      [∀ {m n : SimplexCategory} (φ : m ⟶ n),
        (SheafOfModules.restrictScalars.{w}
          (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
      [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
      [∀ {m n : SimplexCategory} (φ : m ⟶ n),
        ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
      [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
      [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))],
      exactFunctor (Cartesian C J O)
        (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
        (cartesianProperty C J O).ι :=
  sorry

end CategoryTheory.SimplicialSites.Module

