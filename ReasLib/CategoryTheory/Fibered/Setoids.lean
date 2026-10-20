/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- Keep the historical aggregate import surface, including the complete sets-fibred API.
public import ReasLib.CategoryTheory.Fibered.InSets
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom
public import ReasLib.CategoryTheory.Fibered.Setoids.Forgetful
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.Setoids.FromSets

/-!
# Categories fibred in setoids

Compatibility aggregate for the bicategory owner, morphism, forgetful computation and equivalence
bridges, and the canonical inclusion from categories fibred in sets. New direct users should import
the narrow leaf that owns the required construction.
-/
