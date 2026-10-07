module

public import ReasLib.RingTheory.Etale.Weakly.MaximalSubalgebra.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of the maximal weakly etale subalgebra

The maximal weakly etale subalgebra commutes with extension of the base field.  The ambient tensor
map and its codomain restriction are exposed explicitly; only their laws and bijectivity are proof
obligations.

@stack 0CKU
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Subalgebra.maximalWeaklyEtale

variable {K : Type u} [Field K]
variable {L : Type v} [Field L] [Algebra K L]
variable {A : Type w} [CommRing A] [Algebra K A]

-- Local instance justification (instance diamond): view both tensor products as algebras over
-- their right-hand field factor only in this base-change leaf.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The underlying ring homomorphism obtained by tensoring the inclusion
`maximalWeaklyEtale K A -> A` with `L`. -/
@[stacks 0CKU "ambient base-change ring homomorphism"]
def baseChangeRingHom :
    (Subalgebra.maximalWeaklyEtale K A ⊗[K] L) →+* (A ⊗[K] L) :=
  (Algebra.TensorProduct.map (Subalgebra.maximalWeaklyEtale K A).val
    (AlgHom.id K L)).toRingHom

/-- The ambient base-change ring homomorphism commutes with the `L`-algebra maps. -/
theorem baseChangeRingHom_commutes (l : L) :
    baseChangeRingHom (K := K) (L := L) (A := A)
        (algebraMap L (Subalgebra.maximalWeaklyEtale K A ⊗[K] L) l) =
      algebraMap L (A ⊗[K] L) l := sorry

/-- The ambient `L`-algebra homomorphism obtained by tensoring the inclusion of the maximal weakly
etale subalgebra with `L`. -/
@[stacks 0CKU "ambient base-change algebra homomorphism"]
def baseChangeAmbientMap :
    Subalgebra.maximalWeaklyEtale K A ⊗[K] L →ₐ[L] A ⊗[K] L where
  __ := baseChangeRingHom (K := K) (L := L) (A := A)
  commutes' := baseChangeRingHom_commutes (K := K) (L := L) (A := A)

/-- The ambient base-change map lands in the maximal weakly etale `L`-subalgebra of the target. -/
theorem baseChangeAmbientMap_mem (x : Subalgebra.maximalWeaklyEtale K A ⊗[K] L) :
    baseChangeAmbientMap (K := K) (L := L) (A := A) x ∈
      Subalgebra.maximalWeaklyEtale L (A ⊗[K] L) := sorry

/-- Lemma 15.106.4, Stacks `0CKU`: the canonical base-change map from
`maximalWeaklyEtale K A ⊗[K] L` to `maximalWeaklyEtale L (A ⊗[K] L)`. -/
@[stacks 0CKU "canonical base-change map"]
def baseChangeMap :
    Subalgebra.maximalWeaklyEtale K A ⊗[K] L →ₐ[L]
      Subalgebra.maximalWeaklyEtale L (A ⊗[K] L) :=
  (baseChangeAmbientMap (K := K) (L := L) (A := A)).codRestrict
    (Subalgebra.maximalWeaklyEtale L (A ⊗[K] L))
    (baseChangeAmbientMap_mem (K := K) (L := L) (A := A))

/-- Forgetting the codomain restriction recovers the ambient tensor map. -/
theorem baseChangeMap_apply (x : Subalgebra.maximalWeaklyEtale K A ⊗[K] L) :
    (baseChangeMap (K := K) (L := L) (A := A) x : A ⊗[K] L) =
      baseChangeAmbientMap (K := K) (L := L) (A := A) x := sorry

/-- Lemma 15.106.4, Stacks `0CKU`: the canonical base-change map is bijective. -/
@[stacks 0CKU "base change preserves the maximal weakly etale subalgebra"]
theorem baseChangeMap_bijective :
    Function.Bijective (baseChangeMap (K := K) (L := L) (A := A)) := sorry

end Subalgebra.maximalWeaklyEtale
