/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem.Cocycle
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberModulePullback

/-! # Coface cocycles on fiberwise simplicial ringed sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.DerivedModuleSystem

open RingedSite.Simplicial.DerivedModuleSystem

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

variable [UnivLE.{max u v, w}]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/-- Transitions of the cocycle system respect composition of simplex operators after the
canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*`. -/
theorem ofCocycleOnComponents_map_comp (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (CategoryTheory.SimplicialSites.derivedPullbackCompComparisonOf (fiberRingedToposMap F J O φ) (fiberRingedToposMap F J O ψ) (fiberRingedToposMap F J O (ψ ≫ φ))
        ((modulePullbackFunctoriality F J O).pullbackCompIso ψ φ)).app (ofCocycleObj (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) K0 l) ≫
      (ofCocycleTransitionIso (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) K0 α (ψ ≫ φ)).hom =
      (fiberRingedToposMap F J O φ).modulePullbackDerived.map (ofCocycleTransitionIso (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) K0 α ψ).hom ≫
        (ofCocycleTransitionIso (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) K0 α φ).hom :=
  sorry


/-- The last-vertex derived pullbacks with the edge-pullback transitions form a simplicial system. -/
def ofCocycleOnComponents (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α) :
    RingedSite.Simplicial.DerivedModuleSystem (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) :=
  RingedSite.Simplicial.DerivedModuleSystem.of (modulePullbackFunctoriality F J O)
    (ofCocycleObj (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) K0)
    (fun φ ↦ (ofCocycleTransitionIso (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) K0 α φ).hom)
    (ofCocycleOnComponents_map_comp F J O K0 α h)

/-- The object in each degree is the derived pullback along its last vertex. -/
theorem ofCocycleOnComponents_obj (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α) (n : SimplexCategory) :
    (ofCocycleOnComponents F J O K0 α h).obj n =
      ofCocycleObj (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) K0 n := rfl

/-- The transition along a simplex operator is the prescribed edge-pullback composite. -/
theorem ofCocycleOnComponents_map (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α) {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleOnComponents F J O K0 α h).map φ =
      (ofCocycleTransitionIso (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) K0 α φ).hom := rfl

/-- Every transition of the system obtained from a coface cocycle is an isomorphism. -/
theorem ofCocycleOnComponents_isCartesian (K0 : RingedSite.Hom.ModuleDerived.{w} (fiberComponentRingedSite F J O ⦋0⦌))
    (α : (fiberRingedToposMap F J O (SimplexCategory.δ (1 : Fin 2))).modulePullbackDerived.obj K0 ≅
      (fiberRingedToposMap F J O (SimplexCategory.δ (0 : Fin 2))).modulePullbackDerived.obj K0)
    (h : cocycleLeft (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α =
      cocycleRight (fun n ↦ fiberComponentRingedSite F J O n) (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O) α) :

    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
      (ofCocycleOnComponents F J O K0 α h) := sorry

end CategoryTheory.Grothendieck.DerivedModuleSystem
