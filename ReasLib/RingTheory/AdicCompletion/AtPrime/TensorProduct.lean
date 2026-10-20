/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime.Relative

@[expose] public section

/-!
# Tensor maps into completed prime local rings

@stack 07NC

For an algebra map `R → S`, a prime `q` of `S`, and an `R`-algebra map
`A →ₐ[R] S`, this leaf packages the canonical map from the tensor product of
the completed base local ring with `A` to the completed local ring at `q`.
The relative completion algebra is an explicit owner: it depends on the
chosen local-ring map and is therefore not a global instance.
-/

open IsLocalRing
open scoped TensorProduct

universe u v w x

namespace AdicCompletion.AtPrime.TensorProduct

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Tag `07NC`: an `R`-algebra map into `S` induces a tensor map into the completed local ring
at `q`.  The ambient case is obtained from `AlgHom.id R S`, while a subalgebra restriction is
obtained from its inclusion map. -/
@[stacks 07NC "completed local tensor map"]
noncomputable def map (q : Ideal S) [q.IsPrime] (f : A →ₐ[R] S) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
      (Localization.AtPrime (q.under R))) ⊗[R] A →ₐ[
        AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R))]
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  letI : Algebra
      (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) :=
    Relative.mapAlgebra q
  -- Local instance justification (defeq pin): `productLeftAlgHom` needs the scalar tower for
  -- this chosen relative completion algebra, which cannot be registered globally because it
  -- depends on `q`.
  letI : IsScalarTower R
      (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) :=
    Relative.mapAlgebra_isScalarTower q
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId
      (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)))
    (((Algebra.ofId S
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))).restrictScalars R).comp f)

/-- Tag `07NC`: the completed-local tensor map evaluates on a pure tensor by multiplying the
completed local image of its first factor with the dense image of its second factor. -/
@[stacks 07NC "completed local tensor map"]
theorem map_tmul (q : Ideal S) [q.IsPrime] (f : A →ₐ[R] S)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
      (Localization.AtPrime (q.under R))) (a : A) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    map q f (x ⊗ₜ[R] a) =
      AdicCompletion.mapLocal
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x *
        algebraMap S
          (AdicCompletion (maximalIdeal (Localization.AtPrime q))
            (Localization.AtPrime q)) (f a) := sorry

/-- Tag `07NC`: the completed-local tensor map restricts on the completed base factor to the
canonical map of completed local rings. -/
@[stacks 07NC "completed local tensor map"]
theorem map_tmul_one (q : Ideal S) [q.IsPrime] (f : A →ₐ[R] S)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
      (Localization.AtPrime (q.under R))) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    map q f (x ⊗ₜ[R] 1) =
      AdicCompletion.mapLocal
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x := sorry

/-- Tag `07NC`: the completed-local tensor map sends its right tensor factor to the dense image
of its image under the defining algebra map. -/
@[stacks 07NC "completed local tensor map"]
theorem map_one_tmul (q : Ideal S) [q.IsPrime] (f : A →ₐ[R] S) (a : A) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    map q f (1 ⊗ₜ[R] a) =
      algebraMap S
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) (f a) := sorry

/-- Tag `07NC`: if the image of a right tensor factor avoids `q`, then its completed-local
tensor image is a unit. -/
@[stacks 07NC "completed local tensor map"]
theorem map_one_tmul_isUnit (q : Ideal S) [q.IsPrime]
    (f : A →ₐ[R] S) {a : A} (ha : f a ∉ q) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    IsUnit (map q f (1 ⊗ₜ[R] a)) := sorry

variable {B : Type x} [CommRing B] [Algebra R B]

/-- Tag `07NC`: the completed-local tensor map is natural in the algebra map supplied on its
right tensor factor. -/
@[stacks 07NC "completed local tensor map"]
theorem map_comp_tensorMap (q : Ideal S) [q.IsPrime]
    (g : B →ₐ[R] S) (f : A →ₐ[R] B) :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      Relative.mapAlgebra q
    map q (g.comp f) =
      (map q g).comp
        (Algebra.TensorProduct.map
          (AlgHom.id
            (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
              (Localization.AtPrime (q.under R)))
            (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
              (Localization.AtPrime (q.under R)))) f) := sorry

end AdicCompletion.AtPrime.TensorProduct
