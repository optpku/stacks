module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime.TensorProduct

@[expose] public section

/-!
# Products of completed local factors

@stack 07N9

For an algebra `R → S` and a prime `p` of `R`, this leaf owns the canonical
map from the tensor product with the completed local ring at `p` to the
product of the completed local rings at the primes of `S` over `p`.  Its
bijectivity is stated separately under the finite Noetherian hypotheses, so
applications can use coordinate formulas without committing to a chosen
inverse equivalence.
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace AdicCompletion.AtPrime.TensorProduct.Pi

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- The completed local map associated with a prime of `S` lying over `p`
commutes with the original `R`-algebra structures. -/
@[stacks 07N9 "completed local product factor scalar compatibility"]
theorem localMap_apply_algebraMap
    (p : Ideal R) [p.IsPrime] (q : p.primesOver S) (r : R) :
    AdicCompletion.mapLocal
        (Localization.localRingHom p q.1 (algebraMap R S) Ideal.LiesOver.over)
        (algebraMap R
          (AdicCompletion (maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)) r) =
      algebraMap R
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1)) r := sorry

/-- Tag `07N9`: the canonical `R`-algebra map from the completed local ring at `p`
to the completed local factor indexed by `q`. -/
@[stacks 07N9 "completed local product factor"]
noncomputable def baseMap (p : Ideal R) [p.IsPrime] (q : p.primesOver S) :
    AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) →ₐ[R]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1) where
  toRingHom :=
    AdicCompletion.mapLocal
      (Localization.localRingHom p q.1 (algebraMap R S) Ideal.LiesOver.over)
  commutes' := localMap_apply_algebraMap p q

/-- Tag `07N9`: the `q`-coordinate map from the completed tensor product to the
completed local factor at `q`. -/
@[stacks 07N9 "completed local product factor"]
noncomputable def factor (p : Ideal R) [p.IsPrime] (q : p.primesOver S) :
    (AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) ⊗[R] S →ₐ[R]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1) :=
  Algebra.TensorProduct.productMap (baseMap p q)
    ((Algebra.ofId S
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1))).restrictScalars R)

/-- Tag `07N9`: the local-factor map multiplies the completed base image with
the dense image of the right tensor factor. -/
@[stacks 07N9 "completed local product factor"]
theorem factor_tmul (p : Ideal R) [p.IsPrime] (q : p.primesOver S)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) (s : S) :
    factor p q (x ⊗ₜ[R] s) =
      baseMap p q x *
        algebraMap S
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1)) s := sorry

/-- Tag `07N9`: the canonical `R`-algebra map whose factors are the completed local
rings at the primes of `S` lying over `p`. -/
@[stacks 07N9 "completed tensor product decomposition"]
noncomputable def map (p : Ideal R) [p.IsPrime] :
    (AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) ⊗[R] S →ₐ[R]
      ∀ q : p.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1) :=
  AlgHom.pi fun q => factor p q

/-- Tag `07N9`: evaluating the canonical product map at `q` is its local-factor map. -/
@[stacks 07N9 "completed tensor product decomposition"]
theorem map_apply (p : Ideal R) [p.IsPrime]
    (z : (AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) ⊗[R] S)
    (q : p.primesOver S) :
    map p z q = factor p q z := sorry

/-- Tag `07N9`: the canonical product map has the expected pure-tensor formula in
each completed local coordinate. -/
@[stacks 07N9 "completed tensor product decomposition"]
theorem map_tmul (p : Ideal R) [p.IsPrime]
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)) (s : S)
    (q : p.primesOver S) :
    map p (x ⊗ₜ[R] s) q =
      baseMap p q x *
        algebraMap S
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1)) s := sorry

/-- Tag `07N9`: on the completed-base tensor generator, the `q`-coordinate is
the canonical completed local map. -/
@[stacks 07N9 "completed tensor product decomposition"]
theorem map_tmul_one (p : Ideal R) [p.IsPrime]
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p))
    (q : p.primesOver S) :
    map p (x ⊗ₜ[R] (1 : S)) q = baseMap p q x := sorry

/-- Tag `07N9`: on the right tensor generator, every local coordinate is the
dense local image of that generator. -/
@[stacks 07N9 "completed tensor product decomposition"]
theorem map_one_tmul (p : Ideal R) [p.IsPrime] (s : S)
    (q : p.primesOver S) :
    map p
        ((1 : AdicCompletion (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ⊗ₜ[R] s) q =
      algebraMap S
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1)) s := sorry

/-- Stacks Lemma 10.97.8 (tag `07N9`): for a finite algebra over a Noetherian
base, the canonical completed tensor-product map to the product of completed
local factors is bijective. -/
@[stacks 07N9 "completed tensor product decomposition"]
theorem map_bijective [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    Function.Bijective (map (R := R) (S := S) p) := sorry

end AdicCompletion.AtPrime.TensorProduct.Pi
