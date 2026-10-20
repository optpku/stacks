/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A locally finite type monomorphism into the spectrum of the limit of a sequential inverse
system of rings with surjective transition maps and locally nilpotent kernels is an isomorphism
if every stage spectrum factors through it. -/
@[stacks 0CTJ]
theorem isIso_of_stageSpectrum_factorizations
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (T : Scheme.{u}) (f : T ⟶ Spec A_lim.cone.pt) [Mono f] [LocallyOfFiniteType f]
    (h_factor : ∀ n, ∃ g : Spec (A.obj (Opposite.op n)) ⟶ T,
      g ≫ f = Spec.map (A_lim.cone.stageMap n)) :
    IsIso f := sorry

end AlgebraicGeometry.Scheme.Limit
