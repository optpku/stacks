/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Gorenstein.InjectiveDimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizing

/-- If a Noetherian commutative ring has finite injective dimension as a module over
itself, then the regular module concentrated in degree zero is a dualizing complex. -/
theorem ringSingle_of_injectiveDimension_self_ne_top
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : injectiveDimension (ModuleCat.of A A) ≠ ⊤) :
    CategoryTheory.DerivedCategory.IsDualizing
      (ModuleCat.single0 (ModuleCat.of A A)) := sorry

/-- For a Gorenstein ring with `ringKrullDim A ≠ ⊤`, the regular module concentrated
in degree zero is a dualizing complex. -/
theorem ringSingle_of_ringKrullDim_ne_top
    (A : Type u) [CommRing A] [IsGorensteinRing A] (hdim : ringKrullDim A ≠ ⊤) :
    CategoryTheory.DerivedCategory.IsDualizing
      (ModuleCat.single0 (ModuleCat.of A A)) := sorry

/-- Over a Noetherian commutative ring, the regular module in degree zero is dualizing
if and only if the ring has finite injective dimension as a module over itself. -/
theorem ringSingle_iff_injectiveDimension_self_ne_top
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    CategoryTheory.DerivedCategory.IsDualizing (ModuleCat.single0 (ModuleCat.of A A)) ↔
      injectiveDimension (ModuleCat.of A A) ≠ ⊤ := sorry

end CategoryTheory.DerivedCategory.IsDualizing
