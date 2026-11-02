/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal
public import ReasLib.RingTheory.Smooth.EssSmooth

@[expose] public section

/-!
# Artinian local factorisations of algebra homomorphisms

This file attaches Artinian-local, essentially smooth, and flat structure to
the arbitrary-universe factorisation owner `AlgHom.Factorisation.Through`.
It is independent of polynomial presentations and quotient constructions.
-/

universe u v w x

namespace AlgHom.Factorisation

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {f : A →ₐ[R] B}

/-- An arbitrary-universe factorisation through an Artinian local algebra,
with an essentially smooth source map and a flat target map. -/
@[stacks 07FH "Artinian local algebra factorisation"]
structure Artinian (f : A →ₐ[R] B) where
  /-- The intermediate algebra. -/
  mid : Type x
  /-- The commutative-ring structure on the intermediate algebra. -/
  instCommRing : CommRing mid
  /-- The base-algebra structure on the intermediate algebra. -/
  instAlgebra : Algebra R mid
  /-- The underlying arbitrary-universe triangle. -/
  base : Through f mid
  /-- The intermediate algebra is Artinian. -/
  instArtinian : IsArtinianRing mid
  /-- The intermediate algebra is local. -/
  instLocal : IsLocalRing mid
  /-- The source map is essentially smooth. -/
  smooth : base.fromSource.toRingHom.EssSmooth
  /-- The target map is flat. -/
  flat : base.toTarget.toRingHom.Flat

attribute [instance] Artinian.instCommRing Artinian.instAlgebra
  Artinian.instArtinian Artinian.instLocal

namespace Artinian

/-- Attach Artinian-local, smooth, and flat properties to an existing
arbitrary-universe factorisation. -/
def of {M : Type x} [CommRing M] [Algebra R M]
    [IsArtinianRing M] [IsLocalRing M]
    (F : Through f M) (smooth : F.fromSource.toRingHom.EssSmooth)
    (flat : F.toTarget.toRingHom.Flat) : Artinian.{u, v, w, x} f where
  mid := M
  instCommRing := inferInstance
  instAlgebra := inferInstance
  base := F
  instArtinian := inferInstance
  instLocal := inferInstance
  smooth := smooth
  flat := flat

/-- Build an Artinian local factorisation directly from its two maps and
their mathematical properties. -/
def ofMaps {M : Type x} [CommRing M] [Algebra R M]
    [IsArtinianRing M] [IsLocalRing M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (smooth : fromSource.toRingHom.EssSmooth)
    (flat : toTarget.toRingHom.Flat) : Artinian.{u, v, w, x} f :=
  Artinian.of (Through.ofMaps fromSource toTarget factor) smooth flat

/-- The source map of an Artinian local factorisation. -/
abbrev fromSource (F : Artinian.{u, v, w, x} f) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of an Artinian local factorisation. -/
abbrev toTarget (F : Artinian.{u, v, w, x} f) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- The triangle equation carried by an Artinian local factorisation. -/
theorem factor (F : Artinian.{u, v, w, x} f) :
    F.toTarget.comp F.fromSource = f := F.base.factor

namespace mid

/-- The midpoint inherits every prime characteristic of the source. -/
instance charP {p : ℕ} [Fact p.Prime] [CharP A p]
    (F : Artinian.{u, v, w, x} f) : CharP F.mid p := by
  obtain ⟨q, hq⟩ := CharP.exists F.mid
  letI : CharP F.mid q := hq
  have hpM : (p : F.mid) = 0 := by
    rw [← map_natCast F.fromSource.toRingHom p, CharP.cast_eq_zero, map_zero]
  have hqp : q ∣ p := (CharP.cast_eq_zero_iff F.mid q p).mp hpM
  have hqne : q ≠ 1 := by
    intro h
    subst q
    exact CharP.char_ne_one F.mid 1 rfl
  have h_eq : q = p :=
    (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) q hqp).resolve_left hqne
  simpa [h_eq] using hq

end mid

namespace fromSource

/-- The source map is local when its source is Artinian local. -/
instance isLocal [IsArtinianRing A] [IsLocalRing A]
    (F : Artinian.{u, v, w, x} f) : IsLocalHom F.fromSource.toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE F.fromSource.toRingHom).out 4 0).mp
  exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)

end fromSource

namespace toTarget

/-- The target map is local whenever its target is nontrivial. -/
instance isLocal [Nontrivial B] (F : Artinian.{u, v, w, x} f) :
    IsLocalHom F.toTarget.toRingHom := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal F.mid :=
    (IsLocalRing.mem_maximalIdeal a).2 hna
  have hEq : IsLocalRing.maximalIdeal F.mid = nilradical F.mid := by
    calc
      IsLocalRing.maximalIdeal F.mid = Ideal.jacobson (⊥ : Ideal F.mid) :=
        (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal F.mid) bot_ne_top).symm
      _ = (⊥ : Ideal F.mid).radical :=
        IsArtinianRing.jacobson_eq_radical (⊥ : Ideal F.mid)
      _ = nilradical F.mid := rfl
  have hnil : IsNilpotent a := by
    rw [← mem_nilradical, ← hEq]
    exact hmem
  exact (IsNilpotent.not_isUnit (IsNilpotent.map hnil F.toTarget.toRingHom)) ha

end toTarget

/-- Both maps are local under the minimal endpoint hypotheses. -/
theorem local_spec [IsArtinianRing A] [IsLocalRing A] [Nontrivial B]
    (F : Artinian.{u, v, w, x} f) :
    IsLocalHom F.fromSource.toRingHom ∧
      IsLocalHom F.toTarget.toRingHom := by
  exact ⟨inferInstance, inferInstance⟩

/-- The underlying triangle supplied to `Artinian.of` is recovered by
projection. -/
@[simp]
theorem base_of {M : Type x} [CommRing M] [Algebra R M]
    [IsArtinianRing M] [IsLocalRing M]
    (F : Through f M) (smooth : F.fromSource.toRingHom.EssSmooth)
    (flat : F.toTarget.toRingHom.Flat) :
    (Artinian.of F smooth flat).base = F := rfl

/-- The source map supplied to `Artinian.ofMaps` is recovered by projection. -/
@[simp]
theorem fromSource_ofMaps {M : Type x} [CommRing M] [Algebra R M]
    [IsArtinianRing M] [IsLocalRing M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (smooth : fromSource.toRingHom.EssSmooth)
    (flat : toTarget.toRingHom.Flat) :
    (Artinian.ofMaps fromSource toTarget factor smooth flat).fromSource =
      fromSource := rfl

/-- The target map supplied to `Artinian.ofMaps` is recovered by projection. -/
@[simp]
theorem toTarget_ofMaps {M : Type x} [CommRing M] [Algebra R M]
    [IsArtinianRing M] [IsLocalRing M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (smooth : fromSource.toRingHom.EssSmooth)
    (flat : toTarget.toRingHom.Flat) :
    (Artinian.ofMaps fromSource toTarget factor smooth flat).toTarget =
      toTarget := rfl

end Artinian

end AlgHom.Factorisation
