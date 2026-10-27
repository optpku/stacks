/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_10_3_Composition

/-! # Compatibility of formal-system comparisons with their canonical owners -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The coefficient homomorphism on global sections induced by a morphism of spaces. -/
abbrev globalSectionsRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  spaceGlobalSectionsRingMap f

#check (globalSectionsRingMap : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
  (Y ⟶ X) → (globalSectionsRing X ⟶ globalSectionsRing Y))

namespace Modules.ProperFlatFormalSystem

/-- A morphism into derived pushforward induces the change-of-space map on global sections. -/
abbrev globalSectionsMapOfPushforward {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) {K : ModuleDerived Y} {L : ModuleDerived X}
    (α : L ⟶ (Modules.moduleDerivedPushforward f).obj K) :
    (moduleDerivedGlobalSections X).obj L ⟶
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom).obj
        ((moduleDerivedGlobalSections Y).obj K) :=
  spaceGlobalSectionsMapOfPushforward f α

#check (globalSectionsMapOfPushforward : ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S}
  (f : Y ⟶ X) {K : ModuleDerived Y} {L : ModuleDerived X},
  (L ⟶ (Modules.moduleDerivedPushforward f).obj K) →
    ((moduleDerivedGlobalSections X).obj L ⟶
      (CategoryTheory.ModuleCat.derivedRestrictionOfScalars (spaceGlobalSectionsRingMap f).hom).obj
        ((moduleDerivedGlobalSections Y).obj K)))

end Modules.ProperFlatFormalSystem
end AlgebraicGeometry.AlgebraicSpace
