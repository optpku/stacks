/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.RingHom.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjective tensor-product base change

This leaf records the quotient-theoretic behavior of the canonical tensor-product base change of
a surjective ring homomorphism.  The kernel formula is the primary reusable result; preservation
of local nilpotence is a direct property-level companion.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- For a surjective `R`-algebra map, the kernel of its canonical left tensor-product base
change is the extension of its kernel along the base algebra map. -/
theorem includeLeft_ker_eq_map
    (hsurj : Function.Surjective (algebraMap R S)) :
    RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S) =
      (RingHom.ker (algebraMap R S)).map (algebraMap R R') := sorry

/-- A locally nilpotent kernel remains locally nilpotent after canonical left tensor-product
base change of a surjective algebra map. -/
theorem includeLeft_ker_isLocallyNilpotent
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent) :
    (RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S)).IsLocallyNilpotent := sorry

end Algebra.TensorProduct

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace BaseChange

/-- The tensor-product base change of a surjective ring homomorphism is surjective.  This is the
ring-hom presentation of `Algebra.TensorProduct.includeLeft_surjective`. -/
theorem surjective
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hsurj : Function.Surjective f) :
    Function.Surjective (f.baseChange g) := sorry

/-- The kernel of the base change of a surjective ring homomorphism is the image of the original
kernel along the base-change map. -/
theorem ker_eq_map
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hsurj : Function.Surjective f) :
    RingHom.ker (f.baseChange g) = (RingHom.ker f).map g := sorry

/-- Local nilpotence of the kernel of a surjective ring homomorphism is preserved by arbitrary
tensor-product base change. -/
theorem ker_isLocallyNilpotent
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hsurj : Function.Surjective f) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (RingHom.ker (f.baseChange g)).IsLocallyNilpotent := sorry

end BaseChange

end RingHom
