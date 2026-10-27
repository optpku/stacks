/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Comparison

/-! # Formal-completion global-sections comparison interface -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

universe u

#check (AlgebraicGeometry.AlgebraicSpace.spaceGlobalSectionsRingMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (Y ⟶ X) →
    (globalSectionsRing X ⟶ globalSectionsRing Y))

#check (AlgebraicGeometry.AlgebraicSpace.spaceGlobalSectionsMapOfPushforward :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    {K : ModuleDerived Y} {L : ModuleDerived X}, (L ⟶ (Modules.moduleDerivedPushforward f).obj K) →
    ((Modules.moduleDerivedGlobalSections X).obj L ⟶
      (ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom).obj
        ((Modules.moduleDerivedGlobalSections Y).obj K)))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.limitGlobalSectionsMap :
  ∀ {R : CommRingCat.{u}} (X : AlgebraicSpace (Spec R)),
    (R : Type u) →+* globalSectionsRing X)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.limitGlobalSections :
  ∀ {R : CommRingCat.{u}} (X : AlgebraicSpace (Spec R)),
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} (R : Type u)))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System.stageSpaceGlobalSectionsMap :
  ∀ {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : Limits.LimitCone A}
    {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}, (∀ n, Xn n ⟶ Modules.stageSpec A_lim n) → ∀ (n : ℕ),
    (A.obj (Opposite.op n) : Type u) →+* globalSectionsRing (Xn n))
