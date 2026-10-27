/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Coface criteria for cartesian modules on simplicial ringed sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite RingedSite
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

section Modules
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O f)]

/-- A module sheaf on a simplicial total ringed site is cartesian if and only if every coface
comparison is an isomorphism. -/
theorem Module.isCartesian_iff_delta
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    Module.IsCartesian C J O F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (moduleTransition C J O (SimplexCategory.δ j) F) := sorry

/-- An `O`-module whose coface comparisons are isomorphisms is cartesian. -/
instance Module.instIsCartesian_of_isIso_delta
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (moduleTransition C J O (SimplexCategory.δ j) F)] :
    Module.IsCartesian C J O F := sorry

/-- An unbounded derived module on a simplicial total ringed site is cartesian if and only if
every derived coface comparison is an isomorphism. -/
theorem ModuleDerived.isCartesian_iff_delta
    (K : ModuleDerived.{w} (totalRingedSite C J O)) :
    ModuleDerived.IsCartesian C J O K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (moduleDerivedTransition C J O (SimplexCategory.δ j) K) := sorry

/-- An object of `D(O)` whose coface comparisons are isomorphisms is cartesian. -/
instance ModuleDerived.instIsCartesian_of_isIso_delta
    (K : ModuleDerived.{w} (totalRingedSite C J O))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (moduleDerivedTransition C J O (SimplexCategory.δ j) K)] :
    ModuleDerived.IsCartesian C J O K := sorry

end Modules

end CategoryTheory.SimplicialSites
