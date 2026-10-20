/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.IsDualizing

/-- Every complete Noetherian local commutative ring admits an intrinsic dualizing complex. -/
theorem exists_of_completeLocal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A),
      CategoryTheory.DerivedCategory.IsDualizing K := sorry

end CategoryTheory.DerivedCategory.IsDualizing
