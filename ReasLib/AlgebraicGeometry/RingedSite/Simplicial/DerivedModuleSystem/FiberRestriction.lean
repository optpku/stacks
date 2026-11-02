/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberModulePullback
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem

/-!
# Derived-module systems from restriction to fibers
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

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

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

/-- Derived-module systems on the fibers with their canonical pullback comparisons. -/
abbrev DerivedModuleSystemOnComponents :=
  RingedSite.Simplicial.DerivedModuleSystem
    (fun n ↦ fiberComponentRingedSite F J O n)
    (fun φ ↦ fiberRingedToposMap F J O φ) (modulePullbackFunctoriality F J O)

/-- Transitions of the system extracted from `K` respect composition of simplex operators
after the canonical comparison `Lf_φ^* ∘ Lf_ψ^* ⟶ Lf_{ψ ≫ φ}^*`. -/
theorem toDerivedModuleSystem_map_comp
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (CategoryTheory.SimplicialSites.derivedPullbackCompComparisonOf
        (fiberRingedToposMap F J O φ) (fiberRingedToposMap F J O ψ)
        (fiberRingedToposMap F J O (ψ ≫ φ))
        ((modulePullbackFunctoriality F J O).pullbackCompIso ψ φ)).app
        ((moduleDerivedComponent F J O l).obj K) ≫
      moduleDerivedTransition F J O (ψ ≫ φ) K =
      (fiberRingedToposMap F J O φ).modulePullbackDerived.map
          (moduleDerivedTransition F J O ψ K) ≫
        moduleDerivedTransition F J O φ K := sorry

/-- The simplicial system `(K_n, K(φ))` of the derived category of modules attached to an
object `K` of `D(O)`, with `K_n = Lg_n^* K` and `K(φ) : Lf_φ^* K_m ⟶ K_n`. -/
def toDerivedModuleSystem (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    DerivedModuleSystemOnComponents F J O :=
  RingedSite.Simplicial.DerivedModuleSystem.of (modulePullbackFunctoriality F J O)
    (fun n ↦ (moduleDerivedComponent F J O n).obj K)
    (fun φ ↦ moduleDerivedTransition F J O φ K)
    (toDerivedModuleSystem_map_comp F J O K)

/-- The stage object of `toDerivedModuleSystem K` at `n` is `K_n = Lg_n^* K`. -/
theorem toDerivedModuleSystem_obj
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) (n : SimplexCategory) :
    (toDerivedModuleSystem F J O K).obj n = (moduleDerivedComponent F J O n).obj K := rfl

/-- The transition of `toDerivedModuleSystem K` at `φ` is the canonical comparison
`K(φ) : Lf_φ^* K_m ⟶ K_n`. -/
theorem toDerivedModuleSystem_map
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedModuleSystem F J O K).map φ = moduleDerivedTransition F J O φ K := rfl

/-- If `K` is cartesian in `D(O)`, then the extracted system `(K_n, K(φ))` is cartesian. -/
theorem toDerivedModuleSystem_isCartesian
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O))
    (h_cartesian : ModuleDerived.IsCartesian F J O K) :
    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian
      (toDerivedModuleSystem F J O K) := by
  intro m n φ
  exact h_cartesian.isIso_transition φ

/-- Cartesianness of the extracted system is equivalent to cartesianness of `K` in `D(O)`. -/
theorem toDerivedModuleSystem_isCartesian_iff
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)) :
    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian (toDerivedModuleSystem F J O K) ↔
      ModuleDerived.IsCartesian F J O K :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.isIso_transition⟩

/-- Derived restriction to the fibers is natural in a morphism of total derived modules. -/
theorem toDerivedModuleSystemMap_naturality
    {K L : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)} (α : K ⟶ L)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedModuleSystem F J O K).map φ ≫ (moduleDerivedComponent F J O n).map α =
      (fiberRingedToposMap F J O φ).modulePullbackDerived.map
          ((moduleDerivedComponent F J O m).map α) ≫
        (toDerivedModuleSystem F J O L).map φ := by
  change moduleDerivedTransition F J O φ K ≫ _ = _ ≫ moduleDerivedTransition F J O φ L
  unfold moduleDerivedTransition
  exact (NatTrans.naturality _ α).symm

/-- A morphism of total derived modules induces a morphism of their fiberwise
derived-module systems, with components given by derived restriction. -/
def toDerivedModuleSystemMap
    {K L : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)} (α : K ⟶ L) :
    RingedSite.Simplicial.DerivedModuleSystem.Hom (toDerivedModuleSystem F J O K)
      (toDerivedModuleSystem F J O L) :=
  RingedSite.Simplicial.DerivedModuleSystem.homMk (fun n ↦ (moduleDerivedComponent F J O n).map α)
    (toDerivedModuleSystemMap_naturality F J O α)

/-- The component of the induced system morphism at `n` is the derived restriction
of the original morphism to that fiber. -/
theorem toDerivedModuleSystemMap_app
    {K L : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)} (α : K ⟶ L)
    (n : SimplexCategory) :
    (toDerivedModuleSystemMap F J O α).app n =
      (moduleDerivedComponent F J O n).map α := rfl

end CategoryTheory.Grothendieck
