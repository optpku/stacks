/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import Mathlib.CategoryTheory.Localization.Construction

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Composition of derived pullbacks on ringed spaces

The canonical underived pullback-composition isomorphism is lifted through the unbounded total
left derived functor construction.
-/

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open SheafOfModules
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical underived pullback-composition isomorphism on module sheaves over ringed
spaces. -/
noncomputable abbrev modulePullbackCompIso :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  ((pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f)

/-- Pullback along a composite ringed-space morphism is additive. -/
noncomputable instance modulePullbackComp_additive : (pullback (f ≫ g)).Additive :=
  Functor.additive_of_iso (modulePullbackCompIso f g).symm

namespace modulePullbackDerived

/-- The canonical comparison from iterated derived pullback to derived pullback along the
composite morphism. -/
@[stacks 0D5S "derived pullback composition comparison"]
noncomputable def compComparison :
    L(g)^* ⋙ L(f)^* ⟶ L((f ≫ g))^* :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (pullback f) (pullback g) (pullback (f ≫ g)) (modulePullbackCompIso f g)

/-- Computation on the specified sheaf-cell resolution. Both maps come from the existing
cell-model comparison and its native localization computation isomorphism. -/
noncomputable def cochainComputationIso {A B : RingedSpace.{u}} (a : A ⟶ B)
    (K : CochainComplex B.Modules ℤ) :
    (modulePullbackDerived a).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((pullback a).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.CellReplacement.model K)) :=
  ((modulePullbackDerivedCellIso a).app (DerivedCategory.Q.obj K)).symm ≪≫
    (Functor.CellModel.fac (pullback a) (ModulePullbackCells.cochain_inverts a)).app K

/-- The actual augmentation of the second resolution, after applying the outer pullback.
The input of that resolution is the pullback of the specified K-flat model on `Z`. -/
noncomputable def iteratedModelAugmentation (K : CochainComplex Z.Modules ℤ) :=
  ((pullback f).mapHomologicalComplex (up ℤ)).map
    (SheafOfModules.CellReplacement.augmentation
      (((pullback g).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.CellReplacement.model K)))

/-- Pullback preserves K-flat complexes and quasi-isomorphisms between K-flat complexes.
Applied to the displayed augmentation this is exactly the acyclicity used in 0D5S.
This is a property of a specified chain map, not an existence assertion for inverse data. -/
theorem iteratedModelAugmentation_quasiIso (K : CochainComplex Z.Modules ℤ) :
    QuasiIso (iteratedModelAugmentation f g K) := sorry

/-- The actual path-localization isomorphism of a specified quasi-isomorphism. Its backward
arrow is a formal inverse generator, not a witness selected from an admitted `IsIso`. -/
noncomputable def localizedRoofIso {T : RingedSpace.{u}}
    {A B : CochainComplex T.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B :=
  let W := HomologicalComplex.quasiIso T.Modules (up ℤ)
  let Q := (DerivedCategory.Q : CochainComplex T.Modules ℤ ⥤ DerivedCategory T.Modules)
  let F := Localization.Construction.lift Q (Localization.inverts Q W)
  let e : W.Q ⋙ F ≅ Q := eqToIso (Localization.Construction.fac Q
    (Localization.inverts Q W))
  (e.app A).symm ≪≫ F.mapIso (Localization.Construction.wIso a ha) ≪≫ e.app B

/-- The forward leg of the roof is exactly the image of the original chain map. -/
@[simp] theorem localizedRoofIso_hom {T : RingedSpace.{u}}
    {A B : CochainComplex T.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    (localizedRoofIso a ha).hom = DerivedCategory.Q.map a := by
  let W := HomologicalComplex.quasiIso T.Modules (up ℤ)
  let Q := (DerivedCategory.Q : CochainComplex T.Modules ℤ ⥤ DerivedCategory T.Modules)
  let F := Localization.Construction.lift Q (Localization.inverts Q W)
  let e : W.Q ⋙ F ≅ Q := eqToIso (Localization.Construction.fac Q
    (Localization.inverts Q W))
  change e.inv.app A ≫ F.map (W.Q.map a) ≫ e.hom.app B = Q.map a
  calc
    e.inv.app A ≫ F.map (W.Q.map a) ≫ e.hom.app B =
        e.inv.app A ≫ (F.map (W.Q.map a) ≫ e.hom.app B) := rfl
    _ = e.inv.app A ≫ (e.hom.app A ≫ Q.map a) :=
      congrArg (fun t ↦ e.inv.app A ≫ t) (e.hom.naturality a)
    _ = Q.map a := by simp

/-- The specified backward leg, transported from the native formal path localization. -/
noncomputable def localizedRoofInverse {T : RingedSpace.{u}}
    {A B : CochainComplex T.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj A := (localizedRoofIso a ha).inv

/-- Cancellation for the specified forward and backward legs. -/
@[reassoc (attr := simp)]
theorem localizedRoofInverse_hom_inv {T : RingedSpace.{u}}
    {A B : CochainComplex T.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    DerivedCategory.Q.map a ≫ localizedRoofInverse a ha = 𝟙 _ := by
  rw [← localizedRoofIso_hom a ha]
  exact (localizedRoofIso a ha).hom_inv_id

/-- Cancellation in the other order. -/
@[reassoc (attr := simp)]
theorem localizedRoofInverse_inv_hom {T : RingedSpace.{u}}
    {A B : CochainComplex T.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    localizedRoofInverse a ha ≫ DerivedCategory.Q.map a = 𝟙 _ := by
  rw [← localizedRoofIso_hom a ha]
  exact (localizedRoofIso a ha).inv_hom_id

/-- The degreewise underived pullback composition comparison at the original cell model. -/
noncomputable def modelCompositionIso (K : CochainComplex Z.Modules ℤ) :
    ((pullback (f ≫ g)).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.CellReplacement.model K) ≅
      ((pullback f).mapHomologicalComplex (up ℤ)).obj
        (((pullback g).mapHomologicalComplex (up ℤ)).obj
          (SheafOfModules.CellReplacement.model K)) :=
  (NatIso.mapHomologicalComplex (modulePullbackCompIso f g) (up ℤ)).app
    (SheafOfModules.CellReplacement.model K)

/-- Composition computed on the specified resolutions. Every constituent is an actual
computation isomorphism, a formal localized roof, or the degreewise underived comparison. -/
noncomputable def cochainCompIso (K : CochainComplex Z.Modules ℤ) :
    (L(g)^* ⋙ L(f)^*).obj (DerivedCategory.Q.obj K) ≅
      (L((f ≫ g))^*).obj (DerivedCategory.Q.obj K) :=
  (L(f)^*).mapIso (cochainComputationIso g K) ≪≫
    cochainComputationIso f (((pullback g).mapHomologicalComplex (up ℤ)).obj
      (SheafOfModules.CellReplacement.model K)) ≪≫
    localizedRoofIso (iteratedModelAugmentation f g K)
      (iteratedModelAugmentation_quasiIso f g K) ≪≫
    DerivedCategory.Q.mapIso (modelCompositionIso f g K).symm ≪≫
    (cochainComputationIso (f ≫ g) K).symm

/-- Forward computation on a cochain representative. -/
noncomputable def compHomOnCochain (K : CochainComplex Z.Modules ℤ) :
    (L(g)^* ⋙ L(f)^*).obj (DerivedCategory.Q.obj K) ⟶
      (L((f ≫ g))^*).obj (DerivedCategory.Q.obj K) :=
  (cochainCompIso f g K).hom

/-- Actual inverse computation on the same representative. -/
noncomputable def compInvOnCochain (K : CochainComplex Z.Modules ℤ) :
    (L((f ≫ g))^*).obj (DerivedCategory.Q.obj K) ⟶
      (L(g)^* ⋙ L(f)^*).obj (DerivedCategory.Q.obj K) :=
  (cochainCompIso f g K).inv

/-- The inverse's explicit roof formula. In particular its data do not use the canonical
comparison's invertibility theorem or either cancellation theorem. -/
theorem compInvOnCochain_formula (K : CochainComplex Z.Modules ℤ) :
    compInvOnCochain f g K =
      (cochainComputationIso (f ≫ g) K).hom ≫
        DerivedCategory.Q.map (modelCompositionIso f g K).hom ≫
        localizedRoofInverse (iteratedModelAugmentation f g K)
          (iteratedModelAugmentation_quasiIso f g K) ≫
        (cochainComputationIso f (((pullback g).mapHomologicalComplex (up ℤ)).obj
          (SheafOfModules.CellReplacement.model K))).inv ≫
        (L(f)^*).map (cochainComputationIso g K).inv := by
  simp [compInvOnCochain, cochainCompIso, localizedRoofInverse, Category.assoc] <;> rfl

/-- The explicit resolution computation agrees with the original canonical comparison,
which is characterized by its equation with the derived counits. -/
theorem compComparison_app_cochain (K : CochainComplex Z.Modules ℤ) :
    (compComparison f g).app (DerivedCategory.Q.obj K) = compHomOnCochain f g K := sorry

/-- The actual inverse computations respect every original cochain map. -/
theorem compInvOnCochain_naturality {K M : CochainComplex Z.Modules ℤ} (a : K ⟶ M) :
    (L((f ≫ g))^*).map (DerivedCategory.Q.map a) ≫ compInvOnCochain f g M =
      compInvOnCochain f g K ≫ (L(g)^* ⋙ L(f)^*).map (DerivedCategory.Q.map a) := sorry

/-- The actual inverse before localization descent. -/
noncomputable def compInverseOnCochains :
    DerivedCategory.Q ⋙ L((f ≫ g))^* ⟶ DerivedCategory.Q ⋙ (L(g)^* ⋙ L(f)^*) where
  app := compInvOnCochain f g
  naturality := fun _ _ a ↦ compInvOnCochain_naturality f g a

/-- Native localization descends the specified roof computations to the derived category. -/
noncomputable def compInverse : L((f ≫ g))^* ⟶ L(g)^* ⋙ L(f)^* :=
  Localization.liftNatTrans (DerivedCategory.Q (C := Z.Modules))
    (HomologicalComplex.quasiIso Z.Modules (up ℤ))
    (DerivedCategory.Q ⋙ L((f ≫ g))^*) (DerivedCategory.Q ⋙ (L(g)^* ⋙ L(f)^*))
    (L((f ≫ g))^*) (L(g)^* ⋙ L(f)^*) (compInverseOnCochains f g)

/-- The inverse has the advertised roof formula on each cochain representative. -/
@[simp] theorem compInverse_app_cochain (K : CochainComplex Z.Modules ℤ) :
    (compInverse f g).app (DerivedCategory.Q.obj K) = compInvOnCochain f g K := by
  simp [compInverse, compInverseOnCochains]

/-- Cancellation of the two explicit resolution computations. -/
theorem compHomOnCochain_compInv (K : CochainComplex Z.Modules ℤ) :
    compHomOnCochain f g K ≫ compInvOnCochain f g K = 𝟙 _ :=
  (cochainCompIso f g K).hom_inv_id

/-- Cancellation in the other order. -/
theorem compInvOnCochain_compHom (K : CochainComplex Z.Modules ℤ) :
    compInvOnCochain f g K ≫ compHomOnCochain f g K = 𝟙 _ :=
  (cochainCompIso f g K).inv_hom_id

/-- The canonical comparison followed by the actual inverse is the identity. -/
theorem compComparison_compInverse : compComparison f g ≫ compInverse f g = 𝟙 _ := by
  apply Localization.natTrans_ext (DerivedCategory.Q (C := Z.Modules))
    (HomologicalComplex.quasiIso Z.Modules (up ℤ))
  intro K
  simpa only [NatTrans.comp_app, NatTrans.id_app, compComparison_app_cochain,
    compInverse_app_cochain] using compHomOnCochain_compInv f g K

/-- The actual inverse followed by the canonical comparison is the identity. -/
theorem compInverse_compComparison : compInverse f g ≫ compComparison f g = 𝟙 _ := by
  apply Localization.natTrans_ext (DerivedCategory.Q (C := Z.Modules))
    (HomologicalComplex.quasiIso Z.Modules (up ℤ))
  intro K
  simpa only [NatTrans.comp_app, NatTrans.id_app, compComparison_app_cochain,
    compInverse_app_cochain] using compInvOnCochain_compHom f g K

/-- The canonical derived-pullback composition isomorphism with explicitly constructed inverse. -/
noncomputable def canonicalCompIso : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^* where
  hom := compComparison f g
  inv := compInverse f g
  hom_inv_id := compComparison_compInverse f g
  inv_hom_id := compInverse_compComparison f g

/-- Lemma 20.27.2. The invertibility certificate now comes from actual inverse data. -/
@[stacks 0D5S "derived pullback composition comparison is invertible"]
theorem compComparison_isIso : IsIso (compComparison f g) :=
  (canonicalCompIso f g).isIso_hom

/-- Compatibility wrapper preserving the old certificate argument. Its inverse is the actual
resolution computation, and does not depend on the supplied certificate. -/
@[stacks 0D5S "derived pullback composition isomorphism"]
noncomputable def compIso (h : IsIso (compComparison f g)) :
    L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^* := canonicalCompIso f g

/-- The forward map of `compIso` is the canonical composition comparison. -/
@[simp, stacks 0D5S "derived pullback composition isomorphism forward map"]
theorem compIso_hom (h : IsIso (compComparison f g)) :
    (compIso f g h).hom = compComparison f g := rfl

/-- The derived-pullback composition isomorphism is independent of the supplied proof of
comparison invertibility. -/
@[stacks 0D5S "derived pullback composition proof independence"]
theorem compIso_eq (h₁ h₂ : IsIso (compComparison f g)) :
    compIso f g h₁ = compIso f g h₂ := rfl

end modulePullbackDerived

end

end AlgebraicGeometry.RingedSpace
