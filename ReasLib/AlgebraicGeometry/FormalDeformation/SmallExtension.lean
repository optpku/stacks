/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal
public import ReasLib.RingTheory.RingHom.SmallExtension

/-!
# Small extensions of Artinian local algebras

Small extensions of residue-identified Artinian local algebras are characterized
by surjectivity and a nonzero principal kernel annihilated by the source maximal ideal.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The maximal ideal of the stored local ring underlying an Artinian local algebra. -/
def maximalIdeal (B : ArtinianLocalAlgCat Λ k) : Ideal B.carrier :=
  @IsLocalRing.maximalIdeal B.carrier B.carrier.commRing.toCommSemiring B.isLocalRing

/-- A morphism of Artinian local algebras is small when its underlying ring map is small. -/
abbrev IsSmallExtension {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) : Prop :=
  RingHom.IsSmallExtension f.toRingHom

private theorem length_eq_one_iff_principal_annihilated
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) :
    Module.length R I = 1 ↔
      I.IsPrincipal ∧ I ≠ ⊥ ∧ IsLocalRing.maximalIdeal R * I = ⊥ := by
  constructor
  · intro h
    letI : IsSimpleModule R I := Module.length_eq_one_iff.mp h
    refine ⟨Module.isPrincipal_submodule_iff.mp (inferInstance : Module.IsPrincipal R I),
      (IsSimpleModule.isAtom (R := R) (m := I)).ne_bot, ?_⟩
    have hann : Module.annihilator R I = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := I))
    apply le_antisymm ?_ bot_le
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    have hr' : r ∈ Module.annihilator R I := hann.symm ▸ hr
    exact congrArg Subtype.val ((Module.mem_annihilator.mp hr') (⟨s, hs⟩ : I))
  · rintro ⟨hprincipal, hne, hann⟩
    letI : I.IsPrincipal := hprincipal
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal I
    have hxI : x ∈ I := hx.symm ▸ Ideal.mem_span_singleton_self x
    apply Module.length_eq_one_iff.mpr
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨I.nontrivial_iff_ne_bot.mpr hne, ?_⟩
    intro y hy z
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hx.le y.property)
    have haunit : IsUnit a := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro ham
      have haz : a * x = 0 :=
        Ideal.mem_bot.mp (hann ▸ Ideal.mul_mem_mul ham hxI)
      exact hy (Subtype.ext (ha.symm.trans haz))
    obtain ⟨u, rfl⟩ := haunit
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hx.le z.property)
    refine ⟨b * ↑(u⁻¹), Subtype.ext ?_⟩
    change (b * ↑(u⁻¹)) * (y : R) = (z : R)
    calc
      (b * ↑(u⁻¹)) * (y : R) = b * x := by rw [← ha]; simp [mul_assoc]
      _ = (z : R) := hb

/-- A morphism is small exactly when it is surjective with a nonzero principal kernel
annihilated by the source maximal ideal. -/
theorem isSmallExtension_iff {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsSmallExtension f ↔
      Function.Surjective f.toRingHom ∧
        (RingHom.ker f.toRingHom).IsPrincipal ∧
        RingHom.ker f.toRingHom ≠ ⊥ ∧
        maximalIdeal B * RingHom.ker f.toRingHom = ⊥ := by
  letI := B.isLocalRing
  letI := B.isArtinianRing
  letI := A.isLocalRing
  constructor
  · intro h
    exact ⟨h.surjective, (length_eq_one_iff_principal_annihilated _).mp h.ker_length⟩
  · rintro ⟨hsurj, hker⟩
    exact { surjective := hsurj
            ker_length := (length_eq_one_iff_principal_annihilated _).mpr hker }

namespace IsSmallExtension

variable {B A : ArtinianLocalAlgCat Λ k}

/-- A small extension of Artinian local algebras is surjective. -/
theorem surjective {f : B ⟶ A} [IsSmallExtension f] :
    Function.Surjective f.toRingHom :=
  RingHom.IsSmallExtension.surjective

/-- The kernel of a small extension of Artinian local algebras is principal. -/
theorem ker_isPrincipal {f : B ⟶ A} [IsSmallExtension f] :
    (RingHom.ker f.toRingHom).IsPrincipal :=
  ((isSmallExtension_iff f).mp inferInstance).2.1

/-- The kernel of a small extension of Artinian local algebras is nonzero. -/
theorem ker_ne_bot {f : B ⟶ A} [IsSmallExtension f] :
    RingHom.ker f.toRingHom ≠ ⊥ :=
  ((isSmallExtension_iff f).mp inferInstance).2.2.1

/-- The source maximal ideal annihilates the kernel of a small extension. -/
theorem ker_annihilated {f : B ⟶ A} [IsSmallExtension f] :
    maximalIdeal B * RingHom.ker f.toRingHom = ⊥ :=
  ((isSmallExtension_iff f).mp inferInstance).2.2.2

/-- A small extension is surjective with a nonzero principal kernel annihilated
by the source maximal ideal. -/
theorem spec (f : B ⟶ A) [IsSmallExtension f] :
    Function.Surjective f.toRingHom ∧
      (RingHom.ker f.toRingHom).IsPrincipal ∧
      RingHom.ker f.toRingHom ≠ ⊥ ∧
      maximalIdeal B * RingHom.ker f.toRingHom = ⊥ :=
  (isSmallExtension_iff f).mp inferInstance

/-- The kernel of a small extension is generated by a nonzero element annihilated
by every element of the source maximal ideal. -/
theorem exists_generator (f : B ⟶ A) [IsSmallExtension f] :
    ∃ x : B.carrier, x ≠ 0 ∧
      RingHom.ker f.toRingHom = Ideal.span {x} ∧
      ∀ m ∈ maximalIdeal B, m * x = 0 := by
  letI := ker_isPrincipal (f := f)
  obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (RingHom.ker f.toRingHom)
  refine ⟨x, ?_, hx, ?_⟩
  · intro hzero
    exact ker_ne_bot (f := f) (hx.trans (Ideal.span_singleton_eq_bot.mpr hzero))
  · intro m hm
    exact Ideal.mem_bot.mp ((ker_annihilated (f := f)) ▸
      Ideal.mul_mem_mul hm (hx.symm ▸ Ideal.mem_span_singleton_self x))

end IsSmallExtension

end ArtinianLocalAlgCat
