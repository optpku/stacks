/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Separable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom.Differentials
open AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
  [Curve X] [Curve Y] [Smooth X.hom] [Smooth Y.hom]

/-- For a morphism of smooth curves, the differential is nonzero exactly when the relative
differentials are supported on a proper closed subset of the source. -/
theorem differentialNonzero_iff_relativeDifferentialsSupportedProper (f : X ⟶ Y) :
    baseChange f.left.toShHom Y.hom.toShHom ≠ 0 ↔
      ∃ Z : Set X.left, IsClosed Z ∧ Z ≠ Set.univ ∧
        moduleSupport Ω[f.left.toShHom] ⊆ Z := sorry

/-- For a morphism of smooth curves, proper support of the relative differentials is equivalent
to unramifiedness on a nonempty open subset of the source. -/
theorem relativeDifferentialsSupportedProper_iff_existsUnramifiedRestriction (f : X ⟶ Y) :
    (∃ Z : Set X.left, IsClosed Z ∧ Z ≠ Set.univ ∧
        moduleSupport Ω[f.left.toShHom] ⊆ Z) ↔
      ∃ U : X.left.Opens, Nonempty U ∧
        Unramified (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left)) := sorry

/-- For a morphism of smooth curves, unramifiedness on a nonempty open subset of the source is
equivalent to étaleness on a nonempty open subset of the source. -/
theorem existsUnramifiedRestriction_iff_existsEtaleRestriction (f : X ⟶ Y) :
    (∃ U : X.left.Opens, Nonempty U ∧
        Unramified (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left))) ↔
      ∃ U : X.left.Opens, Nonempty U ∧
        Etale (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left)) := sorry

/-- For a morphism of smooth curves, étaleness on a nonempty open subset of the source is
equivalent to a finite separable extension of function fields, with the dominance witness explicit. -/
theorem existsEtaleRestriction_iff_finiteSeparableFunctionFieldExtension (f : X ⟶ Y) :
    (∃ U : X.left.Opens, Nonempty U ∧
        Etale (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left))) ↔
      ∃ hdom : IsDominant f.left,
        @FiniteFunctionFieldExtension _ _ f.left inferInstance inferInstance hdom ∧
          @Algebra.IsSeparable Y.left.functionField X.left.functionField
            inferInstance inferInstance
            (f.left.functionFieldAlgebra
              (@map_genericPoint_eq_of_isDominant _ _ f.left
                inferInstance inferInstance hdom)) := sorry

end AlgebraicGeometry.Curve
