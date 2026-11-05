/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified

/-!
# Pullback of differentials along a universal first-order thickening

The relative-differentials comparison for a commutative triangle can be pulled
back to its source. For a universal first-order thickening of a formally
unramified morphism, this pulled-back comparison is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable (w : i ≫ h' = h)

/-- The canonical map `h^* Ω_{X/B} ⟶ i^* Ω_{Z'/B}` obtained by pulling the
differentials comparison for `h'` back along `i`, after identifying `h^*` with
`i^* ∘ (h')^*` using the commutative triangle `i ≫ h' = h`. -/
noncomputable def pullbackDifferentialsComparison :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      (Modules.pullback i).obj (relativeDifferentials (h' ≫ f)) :=
  (eqToIso (congrArg Modules.pullback w)).inv.app (relativeDifferentials f) ≫
    (Modules.pullbackCompIso i h').inv.app (relativeDifferentials f) ≫
      (Modules.pullback i).map
        (Hom.Differentials.comparison h' (𝟙 B) f (h' ≫ f)
          (Eq.symm (Category.comp_id (h' ≫ f))))

/-- Pulling the canonical relative-differentials comparison of a universal
first-order thickening of a formally unramified morphism back to `Z` is an
isomorphism. -/
instance pullbackDifferentialsComparison_isIso
    (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    IsIso (pullbackDifferentialsComparison i h' h f w) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
