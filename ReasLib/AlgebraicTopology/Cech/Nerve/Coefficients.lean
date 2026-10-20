module

public import ReasLib.AlgebraicTopology.Cech.Existence
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.AlternatingCoface
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient-valued Cech nerves

An arrow with a Cech nerve becomes an augmented cosimplicial object after applying any
contravariant coefficient functor.  This file exposes the ordinary and augmented alternating
coface complexes at that generic level, so site-specific cohomology files only supply the
coefficient functor.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology

noncomputable section

universe u v w z

namespace CategoryTheory.Arrow.Cech

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{z} A]

/-- The augmented Cech nerve of `f`, postcomposed with a contravariant coefficient functor `G`. -/
abbrev augmented (f : Arrow C) [f.HasCechNerve] (G : Cᵒᵖ ⥤ A) :
    CosimplicialObject.Augmented A :=
  (CosimplicialObject.Augmented.whiskeringObj (Cᵒᵖ) A G).obj
    f.augmentedCechNerve.rightOp

/-- The alternating-coface Cech complex of `f` with coefficients in `G`. -/
abbrev complex [Preadditive A]
    (f : Arrow C) [f.HasCechNerve] (G : Cᵒᵖ ⥤ A) :
    CochainComplex A ℕ :=
  (alternatingCofaceMapComplex A).obj (augmented f G).right

/-- The augmented alternating-coface Cech complex of `f` with coefficients in `G`. -/
@[stacks 07A1 "extended coefficient-valued Cech complex"]
noncomputable abbrev extended [Preadditive A] [Limits.HasZeroObject A]
    (f : Arrow C) [f.HasCechNerve] (G : Cᵒᵖ ⥤ A) :
    CochainComplex A ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.extended (augmented f G)

end CategoryTheory.Arrow.Cech
