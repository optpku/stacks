/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Composition of right-derived functors on specified acyclic models

The first additive functor need not be exact. The hypothesis identifies the actual
augmentation whose image under the second functor is a quasi-isomorphism. Its formal
localization inverse supplies the reverse comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe κA κB uA vA uB vB uC vC wA wB wC

namespace CategoryTheory.Functor.KInjectiveModel

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{κA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{κB} B]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]
variable (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
variable (hAcyclic : ∀ K : CochainComplex A ℤ,
  QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κB} B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K)))))

/-- On an original cochain complex, the comparison resolves its `F`-image after resolving
the input. Both directions use the specified augmentation and native factorization maps. -/
def compositionOnInput (K : CochainComplex A ℤ) :
    (derived.{κA} (F ⋙ G)).obj (DerivedCategory.Q.obj K) ≅
      (derived.{κA} F ⋙ derived.{κB} G).obj (DerivedCategory.Q.obj K) :=
  (fac.{κA} (F ⋙ G)).app K ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).app
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K)).symm ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κB} B).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K))))
      (hAcyclic K) ≪≫
    ((fac.{κB} G).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K))).symm ≪≫
    (derived.{κB} G).mapIso ((fac.{κA} F).app K).symm

/-- The model comparison respects every original cochain map. -/
theorem compositionOnInput_naturality {K L : CochainComplex A ℤ} (a : K ⟶ L) :
    (DerivedCategory.Q ⋙ derived.{κA} (F ⋙ G)).map a ≫
        (compositionOnInput F G hAcyclic L).hom =
      (compositionOnInput F G hAcyclic K).hom ≫
        (DerivedCategory.Q ⋙ derived.{κA} F ⋙ derived.{κB} G).map a := sorry

/-- The actual model comparison before localization descent. -/
def compositionOnCochains :
    DerivedCategory.Q ⋙ derived.{κA} (F ⋙ G) ≅
      DerivedCategory.Q ⋙ derived.{κA} F ⋙ derived.{κB} G :=
  NatIso.ofComponents (compositionOnInput F G hAcyclic)
    (fun a ↦ compositionOnInput_naturality F G hAcyclic a)

/-- Deriving the composite agrees with composing the derived functors when the specified
images of source models satisfy the augmentation acyclicity law. -/
def compositionIso : derived.{κA} (F ⋙ G) ≅ derived.{κA} F ⋙ derived.{κB} G :=
  Localization.liftNatIso (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ derived.{κA} (F ⋙ G))
    (DerivedCategory.Q ⋙ derived.{κA} F ⋙ derived.{κB} G)
    (derived.{κA} (F ⋙ G)) (derived.{κA} F ⋙ derived.{κB} G)
    (compositionOnCochains F G hAcyclic)

/-- The descended isomorphism computes on an original complex by the displayed model maps. -/
@[simp]
theorem compositionIso_app (K : CochainComplex A ℤ) :
    (compositionIso F G hAcyclic).app (DerivedCategory.Q.obj K) =
      compositionOnInput F G hAcyclic K := sorry

/-- The comparison carries the unit of the composite to the two-stage derived unit. -/
theorem compositionIso_unit :
    unit (F ⋙ G) ≫ Functor.whiskerLeft DerivedCategory.Q (compositionIso F G hAcyclic).hom =
      (isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).symm (DerivedCategory.Q (C := C))).hom ≫
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ)) (DerivedCategory.Q (C := C))).hom ≫
      RightDerived.Composition.iteratedUnit (unit F) (unit G) := sorry

/-- Native uniqueness transports the displayed comparison to the caller's supplied
total right-derived functors of `F`, `G`, and their composite. -/
def compositionTotalRightDerivedIso
    [Functor.HasRightDerivedFunctor (Functor.RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    [Functor.HasRightDerivedFunctor (Functor.RightDerived.Cochain.toDerived G)
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))]
    [Functor.HasRightDerivedFunctor (Functor.RightDerived.Cochain.toDerived (F ⋙ G))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    Functor.RightDerived.Cochain.functor (F ⋙ G) ≅
      Functor.RightDerived.Cochain.functor F ⋙ Functor.RightDerived.Cochain.functor G :=
  (totalRightDerivedIso.{κA} (F ⋙ G)).symm ≪≫
    compositionIso F G hAcyclic ≪≫
    isoWhiskerRight (totalRightDerivedIso.{κA} F) (derived.{κB} G) ≪≫
    isoWhiskerLeft (Functor.RightDerived.Cochain.functor F) (totalRightDerivedIso.{κB} G)

end CategoryTheory.Functor.KInjectiveModel
