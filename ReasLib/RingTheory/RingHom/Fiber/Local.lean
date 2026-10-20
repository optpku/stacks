/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

/-!
# Local rings of fibers

This leaf owns the prime of a residue-field fiber selected by a point of the
target spectrum, together with the corresponding local fiber ring and its
canonical maps.

-/

noncomputable section

universe u v

open PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct
open scoped Algebra.TensorProduct.Right

namespace PrimeSpectrum

/-- The prime of the residue-field fiber over a specified base prime `p`
corresponding to a prime `q` of `S` that lies over `p`. -/
@[stacks 0H8X "prime of a residue-field fiber"]
noncomputable def fiberPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    PrimeSpectrum (p.asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩

/-- The canonical fiber prime contracts along the right tensor inclusion to
the original prime `q`. -/
@[stacks 0H8X "contraction of a residue-field fiber prime", simp]
theorem fiberPrime_comap_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom
      (fiberPrime p q hq) = q := by
  change ((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrime p q hq)).1 = q
  exact congrArg Subtype.val
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

/-- The ideal underlying the canonical fiber prime contracts along the right
tensor inclusion to the ideal underlying `q`. -/
@[stacks 0H8X "contraction of a residue-field fiber prime", simp]
theorem fiberPrime_comap_asIdeal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Ideal.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom
      (fiberPrime p q hq).asIdeal = q.asIdeal := by
  simpa only [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal (fiberPrime_comap_eq p q hq)

end PrimeSpectrum

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The specialization of `PrimeSpectrum.fiberPrime` at the contraction of
`q : PrimeSpectrum S`, namely the prime of `κ(q ∩ R) ⊗[R] S` corresponding to `q`. -/
def fiberPrimeAt (q : PrimeSpectrum S) : PrimeSpectrum ((q.asIdeal.under R).Fiber S) :=
  PrimeSpectrum.fiberPrime (PrimeSpectrum.comap (algebraMap R S) q) q rfl

/-- The local ring of the fiber at `q : PrimeSpectrum S`. -/
@[stacks 00OL]
def fiberLocalRingAt (q : PrimeSpectrum S) : Type _ :=
  Localization.AtPrime (fiberPrimeAt R S q).asIdeal

/-- The local fiber ring at `q` has the canonical commutative-ring structure. -/
instance fiberLocalRingAtCommRing (q : PrimeSpectrum S) : CommRing (fiberLocalRingAt R S q) := by
  change CommRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local fiber ring at `q` has the canonical local-ring structure. -/
instance fiberLocalRingAtIsLocalRing (q : PrimeSpectrum S) :
    IsLocalRing (fiberLocalRingAt R S q) := by
  change IsLocalRing (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local fiber ring at `q` is canonically an algebra over its fiber ring. -/
instance fiberLocalRingAtFiberAlgebra (q : PrimeSpectrum S) :
    Algebra ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q) := by
  change Algebra ((q.asIdeal.under R).Fiber S)
    (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
  infer_instance

/-- The local fiber ring at `q` is canonically an algebra over `κ(q ∩ R)`. -/
instance fiberLocalRingAtResidueFieldAlgebra (q : PrimeSpectrum S) :
    Algebra (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) :=
  RingHom.toAlgebra <|
    (algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)).comp
      (algebraMap (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S))

/-- The canonical map from `S` to the local fiber ring at `q`. -/
def toFiberLocalRingAt (q : PrimeSpectrum S) : S →+* fiberLocalRingAt R S q :=
  (algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)).comp
    (includeRight : S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom

/-- The local fiber ring at `q` is canonically an `S`-algebra. -/
instance fiberLocalRingAtAlgebra (q : PrimeSpectrum S) : Algebra S (fiberLocalRingAt R S q) :=
  RingHom.toAlgebra (toFiberLocalRingAt R S q)

/-- The local fiber ring at `q` is the localization of its fiber ring at the selected prime. -/
instance fiberLocalRingAtIsLocalization (q : PrimeSpectrum S) :
    IsLocalization.AtPrime (fiberLocalRingAt R S q) (fiberPrimeAt R S q).asIdeal := by
  change IsLocalization.AtPrime (Localization.AtPrime (fiberPrimeAt R S q).asIdeal)
    (fiberPrimeAt R S q).asIdeal
  infer_instance

/-- A local fiber ring is Noetherian whenever its ambient residue-field fiber is Noetherian. -/
noncomputable instance fiberLocalRingAtIsNoetherianRing (q : PrimeSpectrum S)
    [IsNoetherianRing ((q.asIdeal.under R).Fiber S)] :
    IsNoetherianRing (fiberLocalRingAt R S q) :=
  IsLocalization.isNoetherianRing (fiberPrimeAt R S q).asIdeal.primeCompl
    (fiberLocalRingAt R S q) inferInstance

namespace PrimeSpectrum

/-- The canonical prime of the fiber over a target prime contracts back to that
target prime along the canonical right tensor map. -/
@[stacks 0H8X "contraction of a fiber prime along the right tensor map", simp]
theorem fiberPrimeAt_comap_eq (q : PrimeSpectrum S) :
    PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight :
          S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom)
        (fiberPrimeAt R S q) = q := by
  exact PrimeSpectrum.fiberPrime_comap_eq
    (PrimeSpectrum.comap (algebraMap R S) q) q rfl

/-- The ideal underlying the canonical fiber prime contracts back to the
underlying target prime. -/
@[stacks 0H8X "contraction of the ideal of a fiber prime along the right tensor map", simp]
theorem fiberPrimeAt_comap_asIdeal (q : PrimeSpectrum S) :
    Ideal.comap
        ((Algebra.TensorProduct.includeRight :
          S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom)
        (fiberPrimeAt R S q).asIdeal = q.asIdeal := by
  simpa only [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal (fiberPrimeAt_comap_eq R S q)

/-- The canonical fiber prime contracts back to the target prime along the natural target
algebra map to the fiber ring. -/
@[stacks 0H8X "contraction of a residue-field fiber prime along the target algebra map", simp]
theorem fiberPrimeAt_comap_algebraMap_eq (q : PrimeSpectrum S) :
    PrimeSpectrum.comap (algebraMap S ((q.asIdeal.under R).Fiber S))
      (fiberPrimeAt R S q) = q := by
  exact fiberPrimeAt_comap_eq R S q

/-- The ideal underlying the canonical fiber prime contracts back to the target prime along the
natural target algebra map to the fiber ring. -/
@[stacks 0H8X "contraction of the ideal of a residue-field fiber prime along the target algebra map", simp]
theorem fiberPrimeAt_comap_algebraMap_asIdeal (q : PrimeSpectrum S) :
    Ideal.comap (algebraMap S ((q.asIdeal.under R).Fiber S))
        (fiberPrimeAt R S q).asIdeal = q.asIdeal := by
  exact fiberPrimeAt_comap_asIdeal R S q

/-- The contraction to the target ring of the canonical fiber prime lies over
the contraction of `q` to the base ring. -/
theorem fiberPrimeAt_comap_liesOver (q : PrimeSpectrum S) :
    (Ideal.comap
      ((Algebra.TensorProduct.includeRight :
        S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom)
      (fiberPrimeAt R S q).asIdeal).LiesOver (q.asIdeal.under R) := by
  rw [fiberPrimeAt_comap_asIdeal]
  infer_instance

/-- A prime of a fiber is the canonical fiber prime when its contraction along
the canonical right tensor map is the given target prime. -/
theorem fiberPrimeAt_eq_of_comap_eq (q : PrimeSpectrum S)
    (r : PrimeSpectrum ((q.asIdeal.under R).Fiber S))
    (h :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight :
            S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom) r = q) :
    r = fiberPrimeAt R S q := by
  apply (PrimeSpectrum.preimageEquivFiber R S
    (PrimeSpectrum.comap (algebraMap R S) q)).symm.injective
  apply Subtype.ext
  change PrimeSpectrum.comap
      ((Algebra.TensorProduct.includeRight :
        S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom) r =
    PrimeSpectrum.comap
      ((Algebra.TensorProduct.includeRight :
        S →ₐ[R] ((q.asIdeal.under R).Fiber S)).toRingHom)
      (fiberPrimeAt R S q)
  exact h.trans (fiberPrimeAt_comap_eq R S q).symm

end PrimeSpectrum

namespace Algebra.Fiber

/-- The canonical map from the target ring to its local fiber ring factors
through the right tensor inclusion and the localization algebra map. -/
@[simp, stacks 00OL "local fiber ring structural map computation"]
theorem toLocalRingAt_apply (q : PrimeSpectrum S) (s : S) :
    toFiberLocalRingAt R S q s =
      algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)
        ((includeRight : S →ₐ[R] ((q.asIdeal.under R).Fiber S)) s) := rfl

/-- The canonical residue-field action on a local fiber ring factors through its fiber ring. -/
instance isScalarTower_residueField_localRingAt (q : PrimeSpectrum S) :
    IsScalarTower (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
      (fiberLocalRingAt R S q) :=
  ⟨fun r x y => by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    rfl⟩

/-- With the local right-tensor algebra choice, the target action on a local fiber ring factors
through its fiber ring.  This is deliberately a theorem rather than a global instance: the
intermediate `S`-algebra structure is `Algebra.TensorProduct.rightAlgebra`. -/
theorem isScalarTower_localRingAt (q : PrimeSpectrum S) :
    IsScalarTower S ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The canonical map to a local fiber ring restricts on the base ring to the residue-field
scalar action. -/
theorem toLocalRingAt_comp_algebraMap (q : PrimeSpectrum S) :
    (toFiberLocalRingAt R S q).comp (algebraMap R S) =
      (algebraMap (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)).comp
        (algebraMap R (q.asIdeal.under R).ResidueField) := by
  have hmap :
      algebraMap (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) =
        (algebraMap ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q)).comp
          (algebraMap (q.asIdeal.under R).ResidueField
            ((q.asIdeal.under R).Fiber S)) := rfl
  ext r
  simp [toFiberLocalRingAt, hmap]

/-- A base element maps to the local fiber ring through the residue-field scalar action. -/
@[simp]
theorem toLocalRingAt_algebraMap (q : PrimeSpectrum S) (r : R) :
    toFiberLocalRingAt R S q (algebraMap R S r) =
      algebraMap (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q)
        (algebraMap R (q.asIdeal.under R).ResidueField r) := by
  exact DFunLike.congr_fun (toLocalRingAt_comp_algebraMap R S q) r

/-- Under a pair of lying-over prime ideals, the maximal ideal of the base localization maps to
the extension of the base prime in the target localization. -/
theorem map_maximalIdeal_eq
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    Ideal.map
      (Localization.localRingHom p q (algebraMap R S) (Ideal.under_def R q ▸ hq.over))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
    Ideal.map (algebraMap R (Localization.AtPrime q)) p := sorry

end Algebra.Fiber

end

namespace PrimeSpectrum

section

variable {S : Type v} [CommRing S]

/-- The images of a list of elements of `S` form a regular sequence in the local fiber ring at
`q`. -/
def IsRegularInFiberLocalRing (q : PrimeSpectrum S) (R : Type u) [CommRing R] [Algebra R S]
    (fs : List S) : Prop :=
  RingTheory.Sequence.IsRegular (fiberLocalRingAt R S q)
    (fs.map (toFiberLocalRingAt R S q))

end

end PrimeSpectrum
