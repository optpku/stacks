/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    (ha : a ∈ RingHom.ker f) : a • x.1 = 0 := by
  exact (Submodule.mem_torsionBySet_iff _ _).mp x.2 ⟨a, ha⟩

/-- Scalar multiplication by `f r` on the kernel annihilator agrees with the
original `R`-action by `r`. -/
theorem smul (r : R) (x : f.kernelAnnihilator hf E) :
    (f r • x).1 = r • x.1 := by
  change ((RingHom.quotientKerEquivOfSurjective hf).symm (f r) •
    (show Submodule.torsionBySet R E (RingHom.ker f) from x)).1 = r • x.1
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- The kernel annihilator of an injective `R`-module is injective over the
quotient ring represented by the surjection `f`. -/
instance instInjective [Module.Injective R E] :
    Module.Injective S (f.kernelAnnihilator hf E) := by
  constructor
  intro X Y _ _ _ _ i hi g
  letI : Module R X := Module.compHom X f
  letI : Module R Y := Module.compHom Y f
  let iR : X →ₗ[R] Y :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := fun r x => i.map_smul (f r) x }
  let gR : X →ₗ[R] E :=
    { toFun := fun x => (g x).1
      map_add' := fun x y => congrArg Subtype.val (g.map_add x y)
      map_smul' := fun r x =>
        (congrArg Subtype.val (g.map_smul (f r) x)).trans (smul f hf E r (g x)) }
  obtain ⟨l, hl⟩ := Module.Injective.out (R := R) (Q := E) iR hi gR
  have hmem (y : Y) : l y ∈ Submodule.torsionBySet R E (RingHom.ker f) := by
    apply (Submodule.mem_torsionBySet_iff _ _).mpr
    intro a
    rw [← l.map_smul]
    change l (f a.1 • y) = 0
    rw [RingHom.mem_ker.mp a.2, zero_smul, map_zero]
  refine ⟨{
    toFun := fun y => ⟨l y, hmem y⟩
    map_add' := fun y z => Subtype.ext (l.map_add y z)
    map_smul' := ?_ }, ?_⟩
  · intro s y
    obtain ⟨r, rfl⟩ := hf s
    apply Subtype.ext
    exact (l.map_smul r y).trans (smul f hf E r ⟨l y, hmem y⟩).symm
  · intro x
    exact Subtype.ext (hl x)

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
      Submodule.torsionBySet R E (RingHom.ker f) := by
  letI : IsLocalHom f := IsLocalHom.of_surjective f hf
  apply (Submodule.mem_torsionBySet_iff _ _).mpr
  intro a
  have ha : IsLocalRing.residue R a.1 = 0 := by
    apply (RingHom.ResidueField.mapEquivOfSurjective f hf).injective
    rw [map_zero]
    change IsLocalRing.residue S (f a.1) = 0
    rw [RingHom.mem_ker.mp a.2, map_zero]
  rw [← iota.map_smul]
  change iota (IsLocalRing.residue R a.1 *
    (RingHom.ResidueField.mapEquivOfSurjective f hf).symm x) = 0
  rw [ha, zero_mul, map_zero]

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
      toKernelAnnihilatorFun iota f hf x + toKernelAnnihilatorFun iota f hf y := by
  apply Subtype.ext
  change iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm (x + y)) =
    iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm x) +
      iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm y)
  rw [map_add, map_add]

/-- The underlying function of `toKernelAnnihilator` respects the transported
`S`-scalar action. -/
theorem toKernelAnnihilatorFun_smul
    (iota : IsLocalRing.ResidueField R →ₗ[R] E) (f : R →+* S)
    (hf : Function.Surjective f) (s : S) (x : IsLocalRing.ResidueField S) :
    toKernelAnnihilatorFun iota f hf (s • x) =
      s • toKernelAnnihilatorFun iota f hf x := by
  obtain ⟨r, rfl⟩ := hf s
  have he : RingHom.ResidueField.mapEquivOfSurjective f hf (IsLocalRing.residue R r) =
      IsLocalRing.residue S (f r) := rfl
  apply Subtype.ext
  change iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm (f r • x)) =
    (f r • toKernelAnnihilatorFun iota f hf x).1
  rw [RingHom.KernelAnnihilator.smul f hf E]
  change iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm
    (IsLocalRing.residue S (f r) * x)) =
      r • iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm x)
  rw [← he, map_mul, RingEquiv.symm_apply_apply]
  exact iota.map_smul r _

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
    (iota.toKernelAnnihilator f hf).IsInjectiveHull := by
  constructor
  · intro x y h
    apply (RingHom.ResidueField.mapEquivOfSurjective f hf).symm.injective
    apply hiota.injective
    exact congrArg Subtype.val h
  · intro P hP
    let P' : Submodule R E :=
      { carrier := {x | ∃ y : f.kernelAnnihilator hf E, y ∈ P ∧ y.1 = x}
        zero_mem' := ⟨0, P.zero_mem, rfl⟩
        add_mem' := by
          rintro x y ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩
          exact ⟨x' + y', P.add_mem hx' hy', rfl⟩
        smul_mem' := by
          rintro r x ⟨y, hy, rfl⟩
          exact ⟨f r • y, P.smul_mem _ hy, RingHom.KernelAnnihilator.smul f hf E r y⟩ }
    have hP' : P' ≠ ⊥ := by
      intro h
      apply hP
      apply (Submodule.eq_bot_iff P).mpr
      intro x hx
      have hx' : x.1 ∈ P' := ⟨x, hx, rfl⟩
      have hx0 : x.1 = 0 := (Submodule.mem_bot R).mp (h ▸ hx')
      exact Subtype.ext hx0
    obtain ⟨z, ⟨hzrange, hzP'⟩, hz0⟩ :=
      (Submodule.ne_bot_iff _).mp (hiota.essential P' hP')
    obtain ⟨a, ha⟩ := hzrange
    obtain ⟨y, hy, hyz⟩ := hzP'
    refine (Submodule.ne_bot_iff _).mpr ⟨y, ⟨?_, hy⟩, ?_⟩
    · refine ⟨RingHom.ResidueField.mapEquivOfSurjective f hf a, ?_⟩
      apply Subtype.ext
      change iota ((RingHom.ResidueField.mapEquivOfSurjective f hf).symm
        (RingHom.ResidueField.mapEquivOfSurjective f hf a)) = y.1
      rw [RingEquiv.symm_apply_apply]
      exact ha.trans hyz.symm
    · exact fun h => hz0 (hyz.symm.trans (congrArg Subtype.val h))

end LinearMap.IsInjectiveHull
