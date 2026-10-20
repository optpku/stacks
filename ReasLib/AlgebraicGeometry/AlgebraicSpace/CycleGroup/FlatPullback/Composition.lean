/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.FlatComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Composition

/-!
# Composition of flat pullbacks on algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Successive flat pullbacks of a degree-`k` cycle along morphisms of relative
dimensions `s` and `r` agree with pullback along their composite of relative
dimension `r + s`. -/
theorem flatPullback_comp {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [LocallyOfFiniteType f] [Flat f] [RelativeDimension f r]
    (g : Y ⟶ Z) (s : ℕ) [LocallyOfFiniteType g] [Flat g] [RelativeDimension g s]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) (k : ℤ)
    (α : (cycleGroup pZ) δ k) :
    flatPullback pY pX δ f r hf (k + (s : ℤ))
        (flatPullback pZ pY δ g s hg k α) =
      flatPullback pZ pX δ (f ≫ g) (r + s) (by rw [Category.assoc, hg, hf])
        k α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
