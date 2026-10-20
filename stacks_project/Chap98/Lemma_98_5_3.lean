/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap98.Definition_98_5_1
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger.TwoFibreProduct
import StacksCheckRecall

/-!
# 2-fibre products of Rim-Schlessinger categories

The Rim-Schlessinger condition (RS) is stable under 2-fibre products of
categories fibred in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.5.3: if `p : X ⟶ Y` and `q : Z ⟶ Y` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and `X`, `Y`, `Z` all satisfy (RS), then
the 2-fibre product `X ×_Y Z` satisfies (RS). -/
@[stacks 07WR] #check (AlgebraicGeometry.GroupoidsOver.instHasRimSchlessinger_twoFibreProduct :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z],
    HasRimSchlessinger (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q))

end AlgebraicGeometry.GroupoidsOver
