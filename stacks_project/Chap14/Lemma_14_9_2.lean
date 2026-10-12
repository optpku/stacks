/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Products.HomEquiv
import StacksCheckRecall

/-!
@stack 0170
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {U V W : CosimplicialObject C} [HasBinaryProduct U V]

/- Lemma 14.9.2: maps to a product of cosimplicial objects are pairs of maps to its factors. -/
@[stacks 0170]
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
