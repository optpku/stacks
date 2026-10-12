/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-!
# Euler characteristics of coherent modules on algebraic spaces over a field

This leaf owns the Euler characteristic of a coherent module on an algebraic
space proper over a field, as the graded Euler characteristic of its cohomology
modules over that field. The cohomology object is global sections of
`toScheme` of the higher direct image, matching `Modules.cohomologyOver`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {k : Type u} [Field k]
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The dimension of `H^i(X, F)` as a `k`-vector space, for a coherent module on an
algebraic space proper over a field. -/
noncomputable def cohomologyFinrank
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ) : ℕ :=
  Module.finrank k
    ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj
      ((Modules.toScheme (Over.mk σ)).obj (Modules.higherDirectImage π F i)))

/-- `cohomologyFinrank` is the ordinary `k`-dimension of `H^i(X, F)`. -/
theorem cohomologyFinrank_def
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    cohomologyFinrank σ π F i =
      Module.finrank k
        ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj
          ((Modules.toScheme (Over.mk σ)).obj (Modules.higherDirectImage π F i))) :=
  sorry

/-- The Euler characteristic of a coherent module on an algebraic space proper over a
field, as the signed finite sum of the dimensions of its cohomology groups. -/
noncomputable def eulerCharacteristic
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ)
    (fun i : ℕ ↦
      (moduleSpecΓFunctor (R := CommRingCat.of k)).obj
        ((Modules.toScheme (Over.mk σ)).obj (Modules.higherDirectImage π F i)))

/-- Unfold the Euler characteristic into the signed finite sum of cohomology dimensions. -/
theorem eulerCharacteristic_def
    (σ : Spec (CommRingCat.of k) ⟶ S) (π : X ⟶ ofOver (Over.mk σ))
    [Proper π] [Abelian X.Modules] [Abelian (ofOver (Over.mk σ)).Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic σ π F =
      ∑ᶠ i : ℕ,
        ((i : ℤ).negOnePow : ℤ) * (cohomologyFinrank σ π F i : ℤ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
