/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient extensions of rational-function fields

This leaf owns the coefficient-induced map `RatFunc k → RatFunc K` attached to a field
extension `k → K`.  The induced algebra structure is named rather than registered as an
instance: Mathlib keeps `RatFunc.liftAlgebra` scoped because a global registration creates
diamonds with the fraction-field algebra.

@stack 0G31
-/

@[expose] public section

open scoped RatFunc

namespace RatFunc.FieldExtension

universe u v

-- Mathlib keeps the polynomial coefficient algebra out of global search; this is the canonical
-- coefficient owner used only while constructing the named map below.
attribute [local instance] Polynomial.algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- The coefficient map from `k[X]` to `K(X)` induced by `k → K`. -/
@[stacks 0G31 "polynomial coefficient map"]
noncomputable def coefficientMap : Polynomial k →+* RatFunc K :=
  (algebraMap (Polynomial K) (RatFunc K)).comp
    (Polynomial.mapRingHom (algebraMap k K))

/-- The coefficient map is injective for an extension of fields. -/
theorem coefficientMap_injective :
    Function.Injective (coefficientMap (k := k) (K := K)) := sorry

/-- Coefficient denominators remain nonzero after passing to `K(X)`. -/
theorem coefficientMap_nonZeroDivisors :
    nonZeroDivisors (Polynomial k) ≤
      (nonZeroDivisors (RatFunc K)).comap (coefficientMap (k := k) (K := K)) := sorry

/-- The canonical rational-function extension map attached to `k → K`. -/
@[stacks 0G31 "coefficient extension of rational-function fields"]
noncomputable def map : RatFunc k →+* RatFunc K :=
  RatFunc.liftRingHom (coefficientMap (k := k) (K := K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (coefficientMap (k := k) (K := K))
      ((RatFunc.algebraMap_injective (K := K)).comp <|
        Polynomial.map_injective (algebraMap k K) <| RingHom.injective (algebraMap k K)))

/-- The canonical rational-function extension map is injective. -/
@[stacks 0G31 "coefficient extension of rational-function fields is injective"]
theorem map_injective :
    Function.Injective (map (k := k) (K := K)) := sorry

/-- A named, non-instance `RatFunc k`-algebra structure on `RatFunc K`. -/
@[stacks 0G31 "named rational-function algebra owner"]
noncomputable abbrev algebra : Algebra (RatFunc k) (RatFunc K) :=
  (map (k := k) (K := K)).toAlgebra

/-- The canonical extension map restricts to the coefficient map on polynomials. -/
@[simp]
theorem map_algebraMap (p : Polynomial k) :
    map (k := k) (K := K) (algebraMap (Polynomial k) (RatFunc k) p) =
      coefficientMap (k := k) (K := K) p := sorry

/-- The canonical rational-function extension map fixes the polynomial variable. -/
@[simp, stacks 0G31 "coefficient extension fixes the rational-function variable"]
theorem map_X :
    map (k := k) (K := K) RatFunc.X = RatFunc.X := sorry

end RatFunc.FieldExtension
