/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing
public import ReasLib.FieldTheory.Separable.Conormal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Slicing smooth morphisms with separable residue fields

This file constructs smooth relative effective Cartier divisors through
nongeneric fibre points having separable residue-field extensions, as well as
immersed étale slices whose fibres are set-theoretically singletons.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth point with separable residue-field extension that is not generic
in its fibre lies on an effective Cartier divisor in an affine neighbourhood
whose morphism to the base is smooth. -/
theorem SmoothAt.exists_affineOpen_smoothEffectiveCartierDivisor_of_separable
    {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (hf : f.SmoothAt x)
    [hsep : Algebra.IsSeparableOver (S.residueField (f x)) (X.residueField x)]
    (h_not_generic : f.asFiber x ∉ genericPoints (f.fiber (f x))) :
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ D : (U : X.Opens).toScheme.IdealSheafData,
          ⟨x, hxU⟩ ∈ D.support ∧
            IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
              Smooth (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)) := sorry

/-- A morphism smooth at a fibrewise closed point with separable residue-field
extension admits an immersed subscheme through the point which is étale over
the base and whose fibre has image exactly that singleton. -/
theorem SmoothAt.exists_immersion_etale_fiber_eq_singleton
    {X S : Scheme.{u}} {f : X ⟶ S} {x : X} (hf : f.SmoothAt x)
    (hclosed : f.asFiber x ∈ closedPoints (f.fiber (f x)))
    [hsep : Algebra.IsSeparableOver (S.residueField (f x)) (X.residueField x)] :
    ∃ Z : Scheme.{u},
      ∃ i : Z ⟶ X,
        ∃ hxZ : x ∈ Set.range i,
          ∃ hi : IsImmersion i,
            ∃ hetale : Etale (i ≫ f),
              Set.range ((i ≫ f).fiberι (f x) ≫ i) = {x} := sorry

end AlgebraicGeometry.Scheme.Hom
