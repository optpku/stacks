/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative differentials of a fiber product

The relative differentials of a fiber product are canonically the direct sum of the pullbacks
of the relative differentials of its two factors.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.Product

variable {X Y S : Scheme.{u}}

/-- The canonical comparison from the pullback of `Ω[f.toShHom]` along the first projection
to the relative differentials of the fiber product over `S`. -/
noncomputable def fstComparison (f : X ⟶ S) (g : Y ⟶ S) :
    (RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    (({ w := by simpa using (pullback.condition :
          pullback.fst f g ≫ f = pullback.snd f g ≫ g) } :
        CommSq (pullback.fst f g) (pullback.snd f g ≫ g) f (𝟙 S)).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The canonical comparison from the pullback of `Ω[g.toShHom]` along the second projection
to the relative differentials of the fiber product over `S`. -/
noncomputable def sndComparison (f : X ⟶ S) (g : Y ⟶ S) :
    (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom] ⟶
      Ω[(pullback.snd f g ≫ g).toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    (({ w := by simp } :
        CommSq (pullback.snd f g) (pullback.snd f g ≫ g) g (𝟙 S)).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The canonical morphism from the direct sum of the two pulled-back relative-differential
modules to the relative differentials of the fiber product. -/
noncomputable def comparison (f : X ⟶ S) (g : Y ⟶ S) :
    ((RingedSpace.Hom.pullback (pullback.fst f g).toShHom).obj Ω[f.toShHom] ⊞
      (RingedSpace.Hom.pullback (pullback.snd f g).toShHom).obj Ω[g.toShHom]) ⟶
        Ω[(pullback.snd f g ≫ g).toShHom] :=
  biprod.desc (fstComparison f g) (sndComparison f g)

/-- The first projection component is the canonical differential comparison. -/
theorem fstComparison_isComparison (f : X ⟶ S) (g : Y ⟶ S) :
    RingedSpace.Hom.Differentials.IsComparison (fstComparison f g) := sorry

/-- The second projection component is the canonical differential comparison. -/
theorem sndComparison_isComparison (f : X ⟶ S) (g : Y ⟶ S) :
    RingedSpace.Hom.Differentials.IsComparison (sndComparison f g) := sorry

/-- Restricting the product comparison to its first summand gives the first projection
comparison. -/
theorem inl_comparison (f : X ⟶ S) (g : Y ⟶ S) :
    biprod.inl ≫ comparison f g = fstComparison f g := sorry

/-- Restricting the product comparison to its second summand gives the second projection
comparison. -/
theorem inr_comparison (f : X ⟶ S) (g : Y ⟶ S) :
    biprod.inr ≫ comparison f g = sndComparison f g := sorry

/-- The canonical comparison from the direct sum of the pulled-back relative differentials of
the factors to the relative differentials of their fiber product is an isomorphism. -/
instance comparison_isIso (f : X ⟶ S) (g : Y ⟶ S) :
    IsIso (comparison f g) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.Product
