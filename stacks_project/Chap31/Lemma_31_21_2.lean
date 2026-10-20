/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 31.21.2 (1): a regular immersion of schemes is Koszul-regular. -/
@[stacks 063K] #check (AlgebraicGeometry.IsRegularImmersion.isKoszulRegular :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i],
    IsKoszulRegularImmersion i)

/- Lemma 31.21.2 (2): a Koszul-regular immersion of schemes is `H₁`-regular. -/
@[stacks 063K] #check (AlgebraicGeometry.IsKoszulRegularImmersion.isH1Regular :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i],
    IsH1RegularImmersion i)

/- Lemma 31.21.2 (3): an `H₁`-regular immersion of schemes is quasi-regular. -/
@[stacks 063K] #check (AlgebraicGeometry.IsH1RegularImmersion.isQuasiRegular :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsH1RegularImmersion i],
    IsQuasiRegularImmersion i)
