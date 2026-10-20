/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ThreeByThree

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- In a short exact sequence of acyclic two-periodic complexes on finite-length modules,
the determinant of the middle complex is the product of those of the outer complexes. -/
theorem determinant_eq_mul_of_shortExact
    {K₁ K₂ K₃ : TwoPeriodicEndomorphism (ModuleCat.{v} R)}
    (f : Hom K₁ K₂) (g : Hom K₂ K₃) (hzero : f.hom ≫ g.hom = 0)
    (hshort : (ShortComplex.mk f.hom g.hom hzero).ShortExact)
    (hM₁ : IsFiniteLength R K₁.X) (hM₂ : IsFiniteLength R K₂.X)
    (hM₃ : IsFiniteLength R K₃.X)
    (hK₁ : K₁.toCochainComplex.Acyclic) (hK₂ : K₂.toCochainComplex.Acyclic)
    (hK₃ : K₃.toCochainComplex.Acyclic) :
    determinant K₂ hM₂ hK₂ =
      determinant K₁ hM₁ hK₁ * determinant K₃ hM₃ hK₃ := sorry

end CategoryTheory.TwoPeriodicEndomorphism.Hom
