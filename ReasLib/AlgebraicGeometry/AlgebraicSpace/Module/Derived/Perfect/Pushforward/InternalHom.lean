/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Homology.CochainComplex.Bounded

/-! # Perfect pushforward of derived sheaf Hom -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Over a Noetherian target, the derived pushforward of sheaf Hom from a perfect object
to a bounded coherent, relatively flat complex with termwise proper support is perfect. -/
theorem pushforwardDerived_internalHom_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, Proper ((ClosedSubspaceStructure.reduced
      (Closeds.closure (Modules.moduleSupport (G.X i)))).ι ≫ f)) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (InternalHom.obj E (DerivedCategory.Q.obj G))) := sorry

/-- Over a Noetherian target, derived sheaf Hom from a perfect object to a coherent
relatively flat module with proper support has perfect derived pushforward. -/
theorem pushforwardDerived_internalHom_single_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E) (G : Modules X)
    (hG_coherent : G.IsCoherent) (hG_flat : Modules.flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced
      (Closeds.closure (Modules.moduleSupport G))).ι ≫ f)) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (InternalHom.obj E ((DerivedCategory.singleFunctor (Modules X) 0).obj G))) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
