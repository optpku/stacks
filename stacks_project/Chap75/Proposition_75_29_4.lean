/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BoundednessDetection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedExt CategoryTheory.DerivedCategory.DerivedTensor

universe u

/- 0GFI::statement_repair::1. A perfect generator detects boundedness below through
negative Hom and Ext vanishing, global derived Hom, dual-tensor cohomology and
derived global sections, equivalently through the corresponding all-perfect tests. -/
@[stacks 0GFI] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.boundedBelow_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (G E : DerivedQCoh X),
    ModuleDerived.IsPerfect G.obj → IsWeakGenerator G →
    List.TFAE
      [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj G.obj E.obj))
      , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
          IsZero (cohomologyAb X (ModuleDerived.dual G.obj ⊗ᴸ E.obj) i)
      , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
          ((moduleDerivedGlobalSectionsAb X).obj
            (ModuleDerived.dual G.obj ⊗ᴸ E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (ModuleDerived.InternalHom.obj P E.obj))
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
      , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
      ])
