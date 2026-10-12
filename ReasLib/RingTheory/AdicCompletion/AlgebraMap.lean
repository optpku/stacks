/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Adic completion along an algebra map

This leaf constructs the map from the `I`-adic completion of a base ring to
the completion of an algebra along the extended ideal.  Unlike
`AdicCompletion.mapLocal`, the target need not be local.
-/

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The extension of the ideal defining a completion along an algebra map. -/
@[stacks 0CAR "extended ideal of a completion map"]
def extensionIdeal (I : Ideal R) : Ideal S :=
  I.map (algebraMap R S)

/-- The finite quotient map used to construct the completion map along an algebra map. -/
noncomputable def extensionQuotientMap (I : Ideal R) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ (extensionIdeal (S := S) I) ^ n :=
  (Ideal.quotientMap ((extensionIdeal (S := S) I) ^ n) (algebraMap R S)
      ((Ideal.pow_right_mono
          (Ideal.le_comap_map :
            I ≤ Ideal.comap (algebraMap R S) (extensionIdeal (S := S) I))
          n).trans
        (Ideal.le_comap_pow (algebraMap R S) n))).comp
    (AdicCompletion.evalₐ I n)

/-- The finite quotient maps used by `extensionMap` commute with completion transition maps. -/
theorem extensionQuotientMap_compatible (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    ((Ideal.Quotient.factor (Ideal.pow_le_pow_right h) :
        S ⧸ (extensionIdeal (S := S) I) ^ n →+* S ⧸ (extensionIdeal (S := S) I) ^ m)).comp
      (extensionQuotientMap (S := S) I n) =
    extensionQuotientMap (S := S) I m := sorry

/-- The canonical map from the `I`-adic completion of `R` to the completion of `S` along the
extended ideal `I.map (algebraMap R S)`. -/
@[stacks 0CAR "map on extended-ideal completions"]
noncomputable def extensionMap (I : Ideal R) :
    AdicCompletion I R →+* AdicCompletion (extensionIdeal (S := S) I) S :=
  AdicCompletion.liftRingHom (extensionIdeal (S := S) I)
    (extensionQuotientMap (S := S) I)
    (extensionQuotientMap_compatible (S := S) I)

/-- The finite-stage map `extensionQuotientMap` commutes with the canonical maps out of the base
ring. -/
theorem extensionQuotientMap_apply_algebraMap (I : Ideal R) (n : ℕ) (r : R) :
    extensionQuotientMap (S := S) I n (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (S ⧸ (extensionIdeal (S := S) I) ^ n) r := sorry

/-- The `R`-algebra-homomorphism refinement of `extensionQuotientMap`. It reuses the underlying
ring map, so the scalar compatibility is the only additional proof field. -/
@[stacks 0CAR "finite-stage algebra map on extended-ideal completions"]
noncomputable def extensionQuotientAlgHom (I : Ideal R) (n : ℕ) :
    AdicCompletion I R →ₐ[R] S ⧸ (extensionIdeal (S := S) I) ^ n where
  __ := extensionQuotientMap (S := S) I n
  commutes' r := extensionQuotientMap_apply_algebraMap (S := S) I n r

/-- Evaluating `extensionMap` at a finite target quotient recovers its defining quotient map. -/
theorem eval_extensionMap (I : Ideal R) (n : ℕ) :
    (AdicCompletion.evalₐ (extensionIdeal (S := S) I) n).toRingHom.comp
        (extensionMap (S := S) I) =
      extensionQuotientMap (S := S) I n := sorry

/-- The map on completions is compatible with the canonical maps from the base ring. -/
theorem extensionMap_comp_algebraMap (I : Ideal R) :
    (extensionMap (S := S) I).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion (extensionIdeal (S := S) I) S)).comp
        (algebraMap R S) := sorry

/-- The map `extensionMap` sends a dense base element to its canonical dense image. -/
theorem extensionMap_apply_algebraMap (I : Ideal R) (r : R) :
    extensionMap (S := S) I (algebraMap R (AdicCompletion I R) r) =
      algebraMap R (AdicCompletion (extensionIdeal (S := S) I) S) r := sorry

/-- The `R`-algebra-homomorphism refinement of `extensionMap`. This reuses the canonical ring
map and records only the compatibility with the ambient `R`-algebra structures. -/
@[stacks 0CAR "algebra map on extended-ideal completions"]
noncomputable def extensionAlgHom (I : Ideal R) :
    AdicCompletion I R →ₐ[R] AdicCompletion (extensionIdeal (S := S) I) S where
  __ := extensionMap (S := S) I
  commutes' r := extensionMap_apply_algebraMap (S := S) I r

/-- The underlying ring homomorphism of `extensionAlgHom` is `extensionMap`. -/
@[simp]
theorem extensionAlgHom_toRingHom (I : Ideal R) :
    (extensionAlgHom (S := S) I).toRingHom = extensionMap (S := S) I := sorry

/-- Evaluating `extensionAlgHom` at a finite stage recovers the corresponding algebra-valued
quotient map. -/
theorem evalₐ_extensionAlgHom (I : Ideal R) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ (extensionIdeal (S := S) I) n (extensionAlgHom (S := S) I x) =
      extensionQuotientAlgHom (S := S) I n x := sorry

/-- The explicit algebra structure on an extended-ideal completion induced by `extensionMap`.
It is not global because a completion target can be compared through distinct chosen ring maps. -/
@[stacks 0CAR "algebra structure from an extended-ideal completion map"]
noncomputable def extensionAlgebra (I : Ideal R) :
    Algebra (AdicCompletion I R) (AdicCompletion (extensionIdeal (S := S) I) S) :=
  (extensionMap (S := S) I).toAlgebra

/-- The structural map of `extensionAlgebra` is the canonical extended-ideal completion map. -/
theorem algebraMap_extensionAlgebra (I : Ideal R) :
    @algebraMap
        (AdicCompletion I R)
        (AdicCompletion (extensionIdeal (S := S) I) S)
        _ _ (extensionAlgebra (S := S) I) =
      extensionMap (S := S) I := sorry

end AdicCompletion
