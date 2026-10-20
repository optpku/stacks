/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.GeometricPoint
import StacksCheckRecall

/-!
# Length of a quasi-coherent module at a point of an algebraic space

The étale-stalk length of a quasi-coherent `𝒪_X`-module at a geometric point over `x ∈ |X|`
equals a given value `d : ℕ∞` if and only if some, equivalently any, étale scheme chart over
`x` has Zariski-stalk length `d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Lemma 82.4.1: let `S` be a scheme and let `X` be an algebraic space over `S`. Let `F` be a
quasi-coherent `𝒪_X`-module. Let `x ∈ |X|`. Let `d : ℕ∞`. The following are equivalent: the
étale-stalk length `lengthAtGeometricPoint F xbar` equals `d` at a chosen geometric point
`xbar` lying over `x`; for some étale morphism `φ : ofOver U ⟶ X` from a scheme and some `u : U.left`
mapping to `x`, the Zariski-stalk length `lengthOnEtaleChart φ F u` equals `d`; and this holds
for every such étale scheme chart and point over `x`. -/
@[stacks 0EE1]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.lengthAt_tfae :
  ∀ (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (xbar : GeometricPoint X) (hx : xbar.liesOver x) (d : ℕ∞),
    List.TFAE
      [lengthAtGeometricPoint F xbar = d,
        ∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d,
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x → lengthOnEtaleChart φ F u = d])

/- The étale-stalk length of a quasi-coherent module at some geometric point over `x` equals
`d` if and only if some étale scheme chart over `x` has Zariski-stalk length `d`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_lengthAtGeometricPoint_iff :
  ∀ (F : X.Modules) [F.IsQuasicoherent] (x : Points X) (d : ℕ∞),
    (∃ xbar : GeometricPoint X, xbar.liesOver x ∧ lengthAtGeometricPoint F xbar = d) ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d)

/- Some étale scheme chart over `x` has Zariski-stalk length `d` if and only if every étale
scheme chart over `x` has Zariski-stalk length `d`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_lengthOnEtaleChart_iff_forall :
  ∀ (F : X.Modules) [F.IsQuasicoherent] (x : Points X) (d : ℕ∞),
    (∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d) ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
        Points.mapOfOver φ u = x → lengthOnEtaleChart φ F u = d)

end AlgebraicGeometry.AlgebraicSpace.Modules
