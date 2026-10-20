module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Remark_62_5_6_Support

/-!
# Equidimensional families of cycles on fibres

This file records the Stacks condition that the support of a family of
`r`-cycles on fibres is contained in a closed subscheme of relative
dimension at most `r`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.Equidimensional :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}, CyclesOnFibers f r → Prop)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.equidimensional_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} (α : CyclesOnFibers f r),
    Equidimensional α ↔
      ∃ W : X.IdealSheafData,
        support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r)

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
