/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernExactSequence

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/- Lemma 82.30.1 (1): top operational Chern class vanishing for a short exact
sequence with a trivial rank-one submodule. -/
@[stacks 0ES7] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.top_eq_zero_of_unit_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B],
      (δ : Points B → ℤ) → [IsDimensionFunction δ] →
      (f : X ⟶ B) → [QuasiSeparated f] → [LocallyOfFiniteType f] →
      (E F : X.Modules) → (r : ℕ) → 1 ≤ r →
      [SheafOfModules.IsFiniteLocallyFreeOfRank r E] →
      [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F] →
      (ι : 𝟙_ X.Modules ⟶ E) → (q : E ⟶ F) →
      (hzero : ι ≫ q = 0) → (ShortComplex.mk ι q hzero).ShortExact →
      chernClass δ f E r = ChowCohomology.zeroCap δ f (r : ℤ))

/- Lemma 82.30.1 (2): equality of Chern class components below the rank for a
short exact sequence with a trivial rank-one submodule. -/
@[stacks 0ES7] #check
  (AlgebraicGeometry.AlgebraicSpace.ChernClass.component_eq_of_unit_shortExact :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B],
      (δ : Points B → ℤ) → [IsDimensionFunction δ] →
      (f : X ⟶ B) → [QuasiSeparated f] → [LocallyOfFiniteType f] →
      (E F : X.Modules) → (r : ℕ) → 1 ≤ r →
      [SheafOfModules.IsFiniteLocallyFreeOfRank r E] →
      [SheafOfModules.IsFiniteLocallyFreeOfRank (r - 1) F] →
      (ι : 𝟙_ X.Modules ⟶ E) → (q : E ⟶ F) →
      (hzero : ι ≫ q = 0) → (ShortComplex.mk ι q hzero).ShortExact →
      (j : ℕ) → j < r →
      chernClass δ f E j = chernClass δ f F j)

end AlgebraicGeometry.AlgebraicSpace.ChernClass
