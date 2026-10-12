/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Lemma_104_8_3_Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 104.8.3

If `X` is an algebraic stack and `K` is an object of
`D_QCoh(𝒪_{X_flat,fppf})`, then for every morphism of `X_affine` the
canonical derived base-change map of `Lg_! K` is a quasi-isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ModulesOnCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- Lemma 104.8.3: Let `X` be an algebraic stack. Let `K` be an object of
`D_QCoh(𝒪_{X_flat,fppf})`. Then `Lg_! K` satisfies the following property:
for any morphism `x ⟶ x'` of `X_affine` the map
`RΓ(x', Lg_! K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, Lg_! K)` is a quasi-isomorphism.
Here `RΓ` is `chaoticRGamma` after restriction to `X_affine`, and the displayed
`⊗^L` map is `chaoticComparison` of `affineStructureSheaf X`. -/
@[stacks 0H15]
theorem flatFppfLowerShriek_affineComparison_isIso
    (K : DerivedQCohFlatFppf X) {x x' : affineSite X} (f : x ⟶ x') :
    IsIso
      ((chaoticComparison.{u + 1, u, u} (affineStructureSheaf X) f).app
        ((restrictLowerShriekToAffine X).obj K)) :=
  sorry

/-- The restricted object `Lg_! K` on `X_affine` lies in the comparison-map
quasi-coherence property `qcProperty X`. -/
theorem flatFppfLowerShriek_mem_qcProperty (K : DerivedQCohFlatFppf X) :
    qcProperty X ((restrictLowerShriekToAffine X).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
