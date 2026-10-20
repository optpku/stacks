/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.BaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler differentials of quotient maps

This leaf owns the kernel-identified form of the conormal exact sequence for
a surjective map of commutative algebras.

@stack 00RU
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace KaehlerDifferential.Quotient

section Conormal

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S']

/-- The conormal map for a surjection, written using an explicitly chosen
ideal identified with the kernel. -/
@[stacks 00RU "kernel-identified conormal map"]
noncomputable def conormalToBaseChange
    (I : Ideal S) (hI : RingHom.ker (algebraMap S S') = I) :
    I.Cotangent →ₗ[S] S' ⊗[S] Ω[S⁄R] :=
  (KaehlerDifferential.kerCotangentToTensor R S S').comp
    (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap S S')) hI.symm).toLinearMap

/-- The kernel-identified conormal map sends the class of `f ∈ I` to
`1 ⊗ d f`. -/
@[stacks 00RU "kernel-identified conormal map"]
theorem conormalToBaseChange_toCotangent
    (I : Ideal S) (hI : RingHom.ker (algebraMap S S') = I) (x : I) :
    conormalToBaseChange (R := R) (S := S) (S' := S') I hI
        (Ideal.toCotangent I x) =
      1 ⊗ₜ[S] KaehlerDifferential.D R S x := sorry

/-- The conormal map for the canonical quotient `S → S ⧸ I`, promoted to a
linear map over the quotient ring. -/
@[stacks 00RU "quotient-linear conormal map"]
noncomputable def conormalToQuotient (I : Ideal S) :
    I.Cotangent →ₗ[S ⧸ I] (S ⧸ I) ⊗[S] Ω[S⁄R] :=
  (conormalToBaseChange (R := R) (S := S) (S' := S ⧸ I) I (Ideal.mk_ker (I := I))).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- On a cotangent generator, `conormalToQuotient` is the pure tensor of its
universal differential. -/
@[stacks 00RU "quotient-linear conormal map"]
theorem conormalToQuotient_toCotangent (I : Ideal S) (x : I) :
    conormalToQuotient (R := R) I (Ideal.toCotangent I x) =
      1 ⊗ₜ[S] KaehlerDifferential.D R S x := sorry

variable [Algebra R S'] [IsScalarTower R S S']

/-- The kernel-identified conormal map is exact before the Kähler
base-change map for a surjective algebra map. -/
@[stacks 00RU "kernel-identified conormal exact sequence"]
theorem conormalToBaseChange_exact
    (I : Ideal S) (hI : RingHom.ker (algebraMap S S') = I)
    (hsurj : Function.Surjective (algebraMap S S')) :
    Function.Exact (conormalToBaseChange (R := R) (S := S) (S' := S') I hI)
      (KaehlerDifferential.mapBaseChange R S S') := sorry

/-- The quotient-linear conormal map is exact before the Kähler base-change
map for the canonical quotient. -/
@[stacks 00RU "quotient-linear conormal exact sequence"]
theorem conormalToQuotient_exact (I : Ideal S) :
    Function.Exact (conormalToQuotient (R := R) I)
      (KaehlerDifferential.mapBaseChange R S (S ⧸ I)) := by
  change Function.Exact
    (fun x ↦ conormalToBaseChange (R := R) (S := S) (S' := S ⧸ I)
      I (Ideal.mk_ker (I := I)) x)
    (KaehlerDifferential.mapBaseChange R S (S ⧸ I))
  exact conormalToBaseChange_exact (R := R) (S := S) (S' := S ⧸ I)
    I (Ideal.mk_ker (I := I)) Ideal.Quotient.mk_surjective

end Conormal

section BaseChange

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

namespace BaseChange

/-- The algebra structure on `S ⧸ K` over `S ⧸ J` selected by an inclusion
`J ≤ K`.  It is a named value rather than a global instance because the inclusion
is a theorem argument. -/
@[reducible]
def factorAlgebra (J K : Ideal S) (hJK : J ≤ K) :
    Algebra (S ⧸ J) (S ⧸ K) :=
  RingHom.toAlgebra (Ideal.Quotient.factor hJK)

/-- The differential of `J` vanishes after base change to `S ⧸ K`.  Equivalently,
the differentials of generators of `J` lie in `K • Ω[S⁄R]`. -/
def differentialVanishesMod (J K : Ideal S) : Prop :=
  ∀ ⦃x : S⦄, x ∈ J →
    KaehlerDifferential.D R S x ∈ K • (⊤ : Submodule S Ω[S⁄R])

/-- The canonical comparison from Kähler differentials of `S` to those of
`S ⧸ J`, after both sides are base changed to `S ⧸ K`. -/
noncomputable def map (J K : Ideal S) (hJK : J ≤ K) :
    letI : Algebra (S ⧸ J) (S ⧸ K) := factorAlgebra J K hJK
    letI : IsScalarTower S (S ⧸ J) (S ⧸ K) :=
      IsScalarTower.of_algebraMap_eq
        (R := S) (S := S ⧸ J) (A := S ⧸ K) fun _ ↦ rfl
    (S ⧸ K) ⊗[S] Ω[S⁄R] →ₗ[S ⧸ K]
      (S ⧸ K) ⊗[S ⧸ J] Ω[(S ⧸ J)⁄R] :=
  -- Local instance justification (defeq pin): `factorAlgebra` is the unique quotient action
  -- determined by `J ≤ K`; it must remain local because `hJK` is theorem data.
  letI : Algebra (S ⧸ J) (S ⧸ K) := factorAlgebra J K hJK
  letI : IsScalarTower S (S ⧸ J) (S ⧸ K) :=
    IsScalarTower.of_algebraMap_eq
      (R := S) (S := S ⧸ J) (A := S ⧸ K) fun _ ↦ rfl
  KaehlerDifferential.tensorMapBaseChange R S (S ⧸ J) (S ⧸ K)

/-- If the differential of `J` vanishes modulo `K`, the quotient Kähler
base-change comparison is bijective. -/
theorem map_bijective_of_differential
    (J K : Ideal S) (hJK : J ≤ K)
    (hD : differentialVanishesMod (R := R) J K) :
    letI : Algebra (S ⧸ J) (S ⧸ K) := factorAlgebra J K hJK
    letI : IsScalarTower S (S ⧸ J) (S ⧸ K) :=
      IsScalarTower.of_algebraMap_eq
        (R := S) (S := S ⧸ J) (A := S ⧸ K) fun _ ↦ rfl
    Function.Bijective (map (R := R) J K hJK) := sorry

end BaseChange

end BaseChange

end KaehlerDifferential.Quotient
