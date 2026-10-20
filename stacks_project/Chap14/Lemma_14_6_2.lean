/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Products.HomEquiv
import StacksCheckRecall

/-!
@stack 016R
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {U V W : SimplicialObject C} [HasBinaryProduct U V]

/- Lemma 14.6.2: maps to a product of simplicial objects are pairs of maps to its factors. -/
@[stacks 016R]
#check (prod.homEquiv U V W :
  (W ⟶ U ⨯ V) ≃ (W ⟶ U) × (W ⟶ V))

variable (f : W ⟶ U) (g : W ⟶ V)

#check (prod.homEquiv.apply U V (prod.lift f g) :
  prod.homEquiv U V W (prod.lift f g) =
    (prod.lift f g ≫ prod.fst, prod.lift f g ≫ prod.snd))
#check (prod.homEquiv.symm_apply U V (f, g) :
  (prod.homEquiv U V W).symm (f, g) = prod.lift f g)
#check (prod.lift' f g :
  { l : W ⟶ U ⨯ V // l ≫ prod.fst = f ∧ l ≫ prod.snd = g })
#check (prod.hom_ext : ∀ {h k : W ⟶ U ⨯ V},
  h ≫ prod.fst = k ≫ prod.fst → h ≫ prod.snd = k ≫ prod.snd → h = k)
