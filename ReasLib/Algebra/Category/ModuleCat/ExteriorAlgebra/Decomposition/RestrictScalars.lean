/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.Decomposition
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar restriction and the exterior-algebra decomposition

The exterior-algebra decomposition is compatible with semilinear maps after inserting the
canonical comparison between scalar restriction and coproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ModuleCat.exteriorAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The exterior-algebra decomposition commutes with maps into a scalar restriction. -/
@[stacks 01CF "scalar restriction of the exterior-algebra decomposition"]
theorem mapRestrictScalars_decompositionIso_hom
    (f : R →+* S) {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) :
    mapRestrictScalars f g ≫
        (ModuleCat.restrictScalars f).map (decompositionIso N).hom =
      (decompositionIso M).hom ≫
        Limits.Sigma.map (fun n : ℕ ↦
          exteriorPower.mapRestrictScalars f g n) ≫
        (PreservesCoproduct.iso (ModuleCat.restrictScalars f)
          (fun n : ℕ ↦ N.exteriorPower n)).inv := sorry

end ModuleCat.exteriorAlgebra
