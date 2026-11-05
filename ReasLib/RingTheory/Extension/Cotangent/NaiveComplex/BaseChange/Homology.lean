/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of naive cotangent base change

This leaf owns the canonical degree-zero and degree-minus-one maps attached to arbitrary base
change of a naive cotangent complex. The presentation-level chain map and homology maps are
explicit data; only their bijectivity and surjectivity properties remain proof obligations.

@stack 0FUZ
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.H1Cotangent

variable {R S R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']

local notation "S'" => R' ⊗[R] S

-- Local instance justification (instance diamond): select both tensor-factor algebra structures
-- only for the source-facing pushout orientation used by the comparison maps.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

variable (R R' S)

/-- The source half of the degree-minus-one base-change map, from the tensorized cotangent
homology of `S/R` to the cotangent homology of `S'/R`. -/
noncomputable abbrev baseChangeSourceMap :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R S' :=
  LinearMap.liftBaseChange S' (H1Cotangent.map R R S S')

/-- The canonical comparison from tensorized first cotangent homology
`S' ⊗[S] H1Cotangent R S → H1Cotangent R' S'`.

This map need not be surjective for arbitrary base change. The surjective comparison of
Stacks 0FUZ takes homology after tensoring the complex; it is supplied by
`Algebra.Presentation.naiveCotangentBaseChangeH1Comparison`. -/
noncomputable abbrev baseChangeComparison :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S' :=
  (H1Cotangent.map R R' S' S').comp
    (baseChangeSourceMap (R := R) (R' := R') (S := S))

/-- The canonical degree-zero base-change comparison
`S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R']`. -/
@[stacks 0FUZ "canonical H0 base-change comparison"]
noncomputable abbrev baseChangeDegreeZeroComparison :
    S' ⊗[S] Ω[S⁄R] →ₗ[S'] Ω[S'⁄R'] :=
  (KaehlerDifferential.map R R' S' S').comp
    (KaehlerDifferential.mapBaseChange R S S')

/-- Lemma 15.86.2 (1), degree-zero clause (0FUZ): the canonical base-change comparison on
Kähler differentials is bijective. -/
@[stacks 0FUZ "(1), H0 base-change isomorphism"]
theorem baseChangeDegreeZeroComparison_bijective :
    Function.Bijective
      (baseChangeDegreeZeroComparison (R := R) (R' := R') (S := S)) := sorry
/- Proof strategy: expand the comparison as `KaehlerDifferential.map` after `mapBaseChange`; use
the universal property of the tensor-product pushout to identify it with the standard
Kähler-differential base-change equivalence, then take its injective and surjective components. -/

end Algebra.H1Cotangent

namespace Algebra.Presentation

variable {R S R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable {ι σ : Type u}

local notation "S'" => R' ⊗[R] S

-- Local instance justification (instance diamond): reuse both pushout algebra structures only in
-- this specialization of the owner-level comparison.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

/-- The canonical chain map from the base change of a presentation's naive cotangent complex to
the naive cotangent complex of the base-changed presentation. -/
@[stacks 0FUZ "presentation-level naive cotangent base-change map"]
noncomputable abbrev naiveCotangentBaseChangeMap (P : Presentation R S ι σ) :
    Extension.NaiveCotangent.complex P.toExtension.baseChange ⟶
      Extension.NaiveCotangent.complex
        (Generators.baseChange R' P.toGenerators).toExtension :=
  Extension.NaiveCotangent.chainMap (P.baseChangeFromBaseChange R')

/-- The degree-minus-one map induced by presentation base change, with the target identified by
the canonical presentation equivalence. -/
@[stacks 0FUZ "presentation-level H1 base-change comparison"]
noncomputable abbrev naiveCotangentBaseChangeH1Comparison (P : Presentation R S ι σ) :
    LinearMap.ker
        (LinearMap.baseChange S' P.toGenerators.toExtension.cotangentComplex) →ₗ[S']
      (P.baseChange R').toGenerators.toExtension.H1Cotangent :=
  ((P.baseChange R').toGenerators.equivH1Cotangent.symm).toLinearMap ∘ₗ
    H1Cotangent.map R R' S' S' ∘ₗ
      tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators

/-- Lemma 15.86.2 (1), presentation clause (0FUZ): the degree-minus-one comparison attached to
every chosen presentation is surjective. -/
@[stacks 0FUZ "(1), presentation-level H1 base-change surjectivity"]
theorem naiveCotangentBaseChangeH1Comparison_surjective (P : Presentation R S ι σ) :
    Function.Surjective (naiveCotangentBaseChangeH1Comparison (R' := R') P) := sorry
/- Proof strategy: use the explicit base-changed presentation complex.  Lift an element of the
target kernel along the surjective relation-module base-change map, correct its differential using
the bijective degree-zero comparison, and transport through `equivH1Cotangent`. -/

end Algebra.Presentation
