/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Gorenstein.Ring

@[expose] public section

universe u

open CategoryTheory

namespace IsGorensteinRing

/-- For a Noetherian commutative ring, finite injective dimension of the regular
module is equivalent to being Gorenstein with `ringKrullDim A ≠ ⊤`. -/
theorem injectiveDimension_self_ne_top_iff (A : Type u) [CommRing A] [IsNoetherianRing A] :
    injectiveDimension (ModuleCat.of A A) ≠ ⊤ ↔
      IsGorensteinRing A ∧ ringKrullDim A ≠ ⊤ := sorry

/-- A Noetherian commutative ring of finite self-injective dimension is Gorenstein. -/
theorem of_injectiveDimension_self_ne_top (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : injectiveDimension (ModuleCat.of A A) ≠ ⊤) :
    IsGorensteinRing A := sorry

/-- A Noetherian commutative ring of finite self-injective dimension has
`ringKrullDim A ≠ ⊤`. -/
theorem ringKrullDim_ne_top_of_injectiveDimension_self_ne_top
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : injectiveDimension (ModuleCat.of A A) ≠ ⊤) :
    ringKrullDim A ≠ ⊤ := sorry

/-- A Gorenstein ring with `ringKrullDim A ≠ ⊤` has finite injective dimension as a
module over itself. -/
theorem injectiveDimension_self_ne_top (A : Type u) [CommRing A]
    [IsGorensteinRing A] (hdim : ringKrullDim A ≠ ⊤) :
    injectiveDimension (ModuleCat.of A A) ≠ ⊤ := sorry

end IsGorensteinRing
