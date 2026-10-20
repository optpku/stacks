/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap62.Lemma_62_5_1_FiberMap
public import stacks_project.Chap62.Remark_62_5_6_Support_Family
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Restriction

/-!
# Restriction of fibre-cycle families along compatible opens

The restriction construction and its coefficient formula are supplied by the
shared mathematical owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] {r : ℤ}

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.restrict :
  (α : CyclesOnFibers f r) → (U : X.Opens) → (V : Y.Opens) →
    (hUV : U ≤ f ⁻¹ᵁ V) → CyclesOnFibers (f.resLE V U hUV) r)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.restrict_apply :
  ∀ (α : CyclesOnFibers f r) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (v : V.toScheme) (x : (f.resLE V U hUV).fiber v),
    toAlgebraicCycle (restrict α U V hUV) v x =
      toAlgebraicCycle α (V.ι v)
        (fiberMap (f.resLE V U hUV) U.ι V.ι f ⟨(resLE_comp_ι f hUV).symm⟩ v x))

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
