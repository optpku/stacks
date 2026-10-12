/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.RingTheory.LocalRing.ResidueField.Surjective

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The `S`-module of elements of an `R`-module annihilated by the kernel of a
surjection `f : R →+* S`. -/
noncomputable def kernelAnnihilator (f : R →+* S) (hf : Function.Surjective f)
    (E : Type w) [AddCommGroup E] [Module R E] : ModuleCat.{w} S :=
  (ModuleCat.restrictScalars
    (RingHom.quotientKerEquivOfSurjective hf).symm).obj
      (ModuleCat.of (R ⧸ RingHom.ker f)
        (Submodule.torsionBySet R E (RingHom.ker f)))

namespace KernelAnnihilator

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : Function.Surjective f)
  (E : Type w) [AddCommGroup E] [Module R E]

/-- Every element of the kernel annihilator is killed by every element of the
kernel ideal. -/
theorem annihilated (x : f.kernelAnnihilator hf E) (a : R)
    (ha : a ∈ RingHom.ker f) : a • x.1 = 0 := sorry

/-- Scalar multiplication by `f r` on the kernel annihilator agrees with the
original `R`-action by `r`. -/
theorem smul (r : R) (x : f.kernelAnnihilator hf E) :
    (f r • x).1 = r • x.1 := sorry

/-- The kernel annihilator of an injective `R`-module is injective over the
quotient ring represented by the surjection `f`. -/
instance instInjective [Module.Injective R E] :
    Module.Injective S (f.kernelAnnihilator hf E) := sorry

end KernelAnnihilator

end RingHom

namespace LinearMap

variable {R : Type u} {S : Type v} {E : Type w}
  [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [AddCommGroup E] [Module R E]

/-- The value defining the induced residue-field map belongs to the kernel
annihilator. -/
theorem toKernelAnnihilator_mem (f : R →+* S) (hf : Function.Surjective f)
    (iota : IsLocalRing.ResidueField R →ₗ[R] E)
    (x : IsLocalRing.ResidueField S) :
    iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm x) ∈
      Submodule.torsionBySet R E (RingHom.ker f) := sorry

/-- The underlying function of the map from the residue field into the kernel
annihilator. -/
noncomputable def toKernelAnnihilatorFun (iota : IsLocalRing.ResidueField R →ₗ[R] E)
    (f : R →+* S) (hf : Function.Surjective f) (x : IsLocalRing.ResidueField S) :
    f.kernelAnnihilator hf E :=
  ⟨iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm x),
    toKernelAnnihilator_mem f hf iota x⟩

/-- The underlying function of `toKernelAnnihilator` preserves addition. -/
theorem toKernelAnnihilatorFun_add
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (f : R →+* S)
    (hf : Function.Surjective f) (x y : IsLocalRing.ResidueField S) :
    toKernelAnnihilatorFun iota f hf (x + y) =
      toKernelAnnihilatorFun iota f hf x + toKernelAnnihilatorFun iota f hf y := sorry

/-- The underlying function of `toKernelAnnihilator` respects the transported
`S`-scalar action. -/
theorem toKernelAnnihilatorFun_smul
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (f : R →+* S)
    (hf : Function.Surjective f) (s : S) (x : IsLocalRing.ResidueField S) :
    toKernelAnnihilatorFun iota f hf (s • x) =
      s • toKernelAnnihilatorFun iota f hf x := sorry

/-- The `S`-linear map from the residue field of `S` into the submodule of `E`
annihilated by the kernel of `f`, induced by an `R`-linear map from the residue
field of `R`. -/
noncomputable def toKernelAnnihilator (iota : IsLocalRing.ResidueField R →ₗ[R] E)
    (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalRing.ResidueField S →ₗ[S] f.kernelAnnihilator hf E where
  toFun := toKernelAnnihilatorFun iota f hf
  map_add' := toKernelAnnihilatorFun_add iota f hf
  map_smul' := toKernelAnnihilatorFun_smul iota f hf

/-- The induced map into the kernel annihilator has the expected underlying
value. -/
theorem toKernelAnnihilator_apply (iota : IsLocalRing.ResidueField R →ₗ[R] E)
    (f : R →+* S) (hf : Function.Surjective f) (x : IsLocalRing.ResidueField S) :
    (iota.toKernelAnnihilator f hf x).1 =
      iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm x) := rfl

end LinearMap

namespace LinearMap.IsInjectiveHull

variable {R : Type u} {S : Type v} {E : Type w}
  [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- A surjective homomorphism of commutative local rings carries an injective
hull of the source residue field to an injective hull of the target residue
field inside the kernel annihilator. -/
theorem kernelAnnihilator (f : R →+* S) (hf : Function.Surjective f)
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (hiota : iota.IsInjectiveHull) :
    (iota.toKernelAnnihilator f hf).IsInjectiveHull := sorry

end LinearMap.IsInjectiveHull
