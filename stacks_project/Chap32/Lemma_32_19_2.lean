/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.19.2 (1): if `f : X ⟶ Y` is proper and its scheme-theoretic fiber over `y`
has dimension `d`, then the stalk at `y` of `R^i f_* ℱ` vanishes for every quasicoherent
`X`-module `ℱ` and every `i > d`. -/
@[stacks 0E7D] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.stalk_isZero_of_proper_of_fiberDimension_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
      (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
      IsZero
        (AlgebraicGeometry.RingedSpace.stalkModuleCat
          (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ i) y))

/- Lemma 32.19.2 (2): under the same hypotheses, one affine open neighborhood `V` of `y`
exists such that the restricted morphism `f ∣_ V` has quasi-compact and quasi-separated source
and target, its quasicoherent higher direct images vanish above `d` after arbitrary cartesian
base change, its degree-`d` higher direct image satisfies the projection formula, and formation
of that higher direct image commutes with every further cartesian base change. -/
@[stacks 0E7D] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.exists_affineOpen_topDegreeBaseChange_of_proper_of_fiberDimension_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
      (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)),
      ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V),
        AlgebraicGeometry.Scheme.HigherDirectImage.TopDegreeBaseChange (f ∣_ V) d)
