/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_18_1
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# 2-fibre products of strong Rim-Schlessinger categories

The strong Rim-Schlessinger condition (RS*) is stable under 2-fibre products of
categories fibred in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.18.3: if `p : X ⟶ Y` and `q : Z ⟶ Y` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and `X`, `Y`, `Z` all satisfy (RS*), then
the 2-fibre product `X ×_Y Z` satisfies (RS*). -/
@[stacks 0CXQ]
instance instHasStrongRimSchlessinger_twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
    [HasStrongRimSchlessinger Z] :
    HasStrongRimSchlessinger (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
