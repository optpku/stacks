/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Restriction

/-!
# Compatibility of composition of fibre-cycle families with open restriction

Composition commutes with restriction to compatible opens of the source and
intermediate scheme, after the canonical identification of the composite fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- The canonical comparison of fibres of the two equal structure morphisms
from a compatible open of the source to the base. -/
noncomputable def compRestrictFiberMap {S X Y : Scheme.{u}} (p : Y ⟶ S)
    (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (s : S) :
    (U.ι ≫ f ≫ p).fiber s ⟶ (f.resLE V U hUV ≫ V.ι ≫ p).fiber s :=
  eqToHom (congrArg (fun g : U.toScheme ⟶ S ↦ g.fiber s) (by
    calc
      U.ι ≫ f ≫ p = (U.ι ≫ f) ≫ p := (Category.assoc _ _ _).symm
      _ = (f.resLE V U hUV ≫ V.ι) ≫ p :=
        congrArg (fun g ↦ g ≫ p) (resLE_comp_ι f hUV).symm
      _ = f.resLE V U hUV ≫ V.ι ≫ p := Category.assoc _ _ _))

/-- Composition of families of cycles of nonnegative degrees commutes with
restriction to compatible opens, coefficientwise under the canonical fibre
comparison. -/
theorem comp_restrict {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : CyclesOnFibers f (r : ℤ)) (β : CyclesOnFibers p (e : ℤ)) (U : X.Opens)
    (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (s : S)
    (x : (U.ι ≫ f ≫ p).fiber s) :
    toAlgebraicCycle (restrictOver (comp α β) U) s x =
      toAlgebraicCycle
        (comp (restrict α U V hUV) (restrictOver β V))
        s (compRestrictFiberMap p f U V hUV s x) := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
