/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Flat.Locus.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of closed subsets in flatness loci

Stability of closed-subset flatness conditions under tensor-product base change.
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

namespace Ideal.FlatLocus

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

-- Local instance justification (instance diamond): select the canonical target-side algebra
-- structure on the tensor-product base change.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- Local declaration justification (source-local notation): name the tensor-product target ring in the paired base-change theorem signatures.
local notation "S'" => S ⊗[R] R'
-- Local declaration justification (source-local notation): name the corresponding base-changed module using the selected target-side scalar path.
local notation "M'" => S' ⊗[S] M

/-- A closed subset contained in the flatness locus remains so after base change, provided the
new defining ideal contains the image of the old one. -/
@[stacks 052X "closed-subset flatness locus under base change"]
theorem baseChange_of_map_le {K : Ideal S} {K' : Ideal S'}
    (hflat : zeroLocus (K : Set S) ⊆ Module.flatOverBaseLocus R S M)
    (hK' : Ideal.map (algebraMap S S') K ≤ K') :
    zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M' := sorry

/-- The closed-fiber flatness condition for an ideal of the base ring is preserved
after any base change and enlargement of the extended ideal. -/
@[stacks 052X "Lemma 15.18.1"]
theorem baseChange {I : Ideal R} {I' : Ideal R'}
    (hflat : zeroLocus (I.map (algebraMap R S) : Set S) ⊆
      Module.flatOverBaseLocus R S M)
    (hI' : I.map (algebraMap R R') ≤ I') :
    zeroLocus (I'.map (algebraMap R' S') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := sorry

section TensorTower

variable {R'' : Type*} [CommRing R'']
variable [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']

-- Local declaration justification (source-local notation): name the source tensor-product ring in the paired tensor-tower theorem signatures.
local notation "S₁" => S ⊗[R] R'
-- Local declaration justification (source-local notation): name the target tensor-product ring determined by the selected scalar-tower path.
local notation "S₂" => S ⊗[R] R''
-- Local declaration justification (source-local notation): name the source base-changed module in the paired tensor-tower theorem signatures.
local notation "M₁" => S₁ ⊗[S] M
-- Local declaration justification (source-local notation): name the target base-changed module using the selected scalar-tower path.
local notation "M₂" => S₂ ⊗[S] M

omit [Module R M] [IsScalarTower R S M] in
/-- A closed-subset flatness condition ascends along a further algebra map in a tensor-product
tower when the target ideal contains the image of the source ideal. -/
@[stacks 05LR "closed-subset flatness along a tensor-product tower"]
theorem tensorTower_of_map_le {K₁ : Ideal S₁} {K₂ : Ideal S₂}
    (hflat : zeroLocus (K₁ : Set S₁) ⊆ Module.flatOverBaseLocus R' S₁ M₁)
    (hK₂ : Ideal.map
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (IsScalarTower.toAlgHom R R' R'')).toRingHom K₁ ≤ K₂) :
    zeroLocus (K₂ : Set S₂) ⊆ Module.flatOverBaseLocus R'' S₂ M₂ := sorry

omit [Module R M] [IsScalarTower R S M] in
/-- Closed-fiber flatness with an additional algebra ideal is preserved by a
further base change and enlargement of the base ideal. -/
@[stacks 05LR "Lemma 15.19.2"]
theorem tensorTower_add (J : Ideal S) (I' : Ideal R') (I'' : Ideal R'')
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hflat : zeroLocus
      ((Ideal.map (algebraMap R' S₁) I' + Ideal.map (algebraMap S S₁) J : Ideal S₁) :
        Set S₁) ⊆ Module.flatOverBaseLocus R' S₁ M₁) :
    zeroLocus
        ((Ideal.map (algebraMap R'' S₂) I'' + Ideal.map (algebraMap S S₂) J : Ideal S₂) :
          Set S₂) ⊆
      Module.flatOverBaseLocus R'' S₂ M₂ := sorry

end TensorTower

end Ideal.FlatLocus
