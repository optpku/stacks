/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.CartesianOver

open CategoryTheory
open CategoryTheory.SimplicialObject

universe v u

variable {C : Type u} [Category.{v} C] (X : SimplicialObject C)

/- Cartesian simplicial objects over a base form the full subcategory of cartesian
structure morphisms. -/
#check (CartesianOver.ofHom :
  ∀ {Y : SimplicialObject C} (a : Y ⟶ X), IsCartesian a → CartesianOver X)

/- The cartesian condition agrees with equifiberedness of the structure morphism. -/
#check (isCartesian_iff_equifibered :
  ∀ {Y : SimplicialObject C} (a : Y ⟶ X), IsCartesian a ↔ NatTrans.Equifibered a)
