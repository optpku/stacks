/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over

/-!
# Fibre-cycle actions in a slice category

The fibre-cycle action can be transported to the grading defined by the
structure morphism of a scheme over a fixed base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- Transport of the fibre-cycle action along `Over.w`, so the output is graded
by the structure morphism of the source rather than the composite `f.left ≫ Y.hom`. -/
noncomputable def capOver
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {r : ℤ} (α : CyclesOnFibers f.left r) (e : ℤ) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) e →+
      CycleGroup X.left (X.hom.relativeDimensionFunction δ) (r + e) :=
  (AddEquiv.toAddMonoidHom
      (AddEquiv.cast (M := fun d : X.left → ℤ ↦ CycleGroup X.left d (r + e))
        (Scheme.Hom.relativeDimensionFunction_congr f.w δ))).comp
    (capHom Y.hom f.left δ α e)

/-- Evaluating `capOver` transports `capHom` along the equality of relative
dimension functions induced by `Over.w`. -/
theorem capOver_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {r : ℤ} (α : CyclesOnFibers f.left r) (e : ℤ)
    (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) e) :
    capOver δ f α e β =
      AddEquiv.cast (M := fun d : X.left → ℤ ↦ CycleGroup X.left d (r + e))
        (Scheme.Hom.relativeDimensionFunction_congr f.w δ)
        (capHom Y.hom f.left δ α e β) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
