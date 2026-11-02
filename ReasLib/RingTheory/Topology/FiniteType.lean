/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

universe u v w

variable (R : Type u) (A : Type v)

/-- An algebra is topologically of finite type when a finite-variable polynomial
algebra maps densely into it. -/
class Algebra.TopologicallyOfFiniteType [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] : Prop where
  /-- A finite-variable polynomial algebra map with dense range exists. -/
  out : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f

namespace Algebra
namespace TopologicallyOfFiniteType

variable {R A}
variable [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A]

/-- An algebraically finite-type algebra is topologically of finite type. -/
instance (priority := 100) ofFiniteType [Algebra.FiniteType R A] :
    TopologicallyOfFiniteType R A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact ⟨⟨n, f, hf.denseRange⟩⟩

/-- A dense finite-variable polynomial algebra map supplies topological finite type. -/
theorem of_denseRange {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : DenseRange f) :
    TopologicallyOfFiniteType R A :=
  ⟨⟨n, f, hf⟩⟩

/-- A topologically finite-type algebra has a dense finite-variable polynomial map. -/
theorem exists_denseRange_mvPolynomial [TopologicallyOfFiniteType R A] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f :=
  (inferInstance : TopologicallyOfFiniteType R A).out

/-- Topological finite type is equivalent to admitting a dense finite-variable polynomial map. -/
theorem iff :
    TopologicallyOfFiniteType R A ↔
      ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), DenseRange f :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

/-- Topological finite type is equivalent to having a finitely generated dense subalgebra. -/
theorem iff_dense_adjoin :
    TopologicallyOfFiniteType R A ↔
      ∃ s : Finset A, Dense (Algebra.adjoin R (s : Set A) : Set A) := by
  constructor
  · intro h
    obtain ⟨n, f, hf⟩ := h.out
    have hfg : f.range.FG := by
      simpa only [Algebra.map_top] using
        (Algebra.FiniteType.out (R := R) (A := MvPolynomial (Fin n) R)).map f
    obtain ⟨s, hs⟩ := hfg
    refine ⟨s, ?_⟩
    rw [hs]
    exact hf
  · rintro ⟨s, hs⟩
    let S := Algebra.adjoin R (s : Set A)
    haveI : Algebra.FiniteType R S :=
      (Subalgebra.fg_iff_finiteType S).mp ⟨s, rfl⟩
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType R S)
    apply of_denseRange (S.val.comp f)
    have hrange : Set.range (S.val.comp f) = (S : Set A) := by
      ext a
      constructor
      · rintro ⟨p, rfl⟩
        exact (f p).property
      · intro ha
        obtain ⟨p, hp⟩ := hf ⟨a, ha⟩
        exact ⟨p, congrArg Subtype.val hp⟩
    change Dense (Set.range (S.val.comp f))
    rwa [hrange]

end TopologicallyOfFiniteType
end Algebra

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- A ring homomorphism is topologically of finite type when its target is so over its source. -/
def TopologicallyOfFiniteType (f : A →+* B) : Prop :=
  @Algebra.TopologicallyOfFiniteType A B _ _ f.toAlgebra _

/-- The algebra-map and ring-homomorphism formulations of topological finite type agree. -/
theorem topologicallyOfFiniteType_algebraMap [Algebra A B] :
    (algebraMap A B).TopologicallyOfFiniteType ↔ Algebra.TopologicallyOfFiniteType A B := by
  rw [TopologicallyOfFiniteType, toAlgebra_algebraMap]

/-- For a continuous map of topological rings, topological finite type is the
dense-range condition for a finite-variable polynomial ring homomorphism. -/
theorem topologicallyOfFiniteType_iff_denseRange
    [TopologicalSpace A] [IsTopologicalRing A] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    φ.TopologicallyOfFiniteType ↔
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) A →+* B),
        g.comp (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) = φ ∧ DenseRange g := by
  letI : Algebra A B := φ.toAlgebra
  constructor
  · intro h
    obtain ⟨n, f, hf⟩ := h.out
    refine ⟨n, f.toRingHom, ?_, hf⟩
    ext a
    exact f.commutes a
  · rintro ⟨n, g, hg, hd⟩
    refine ⟨⟨n, { g with commutes' := ?_ }, hd⟩⟩
    intro a
    exact congrArg (fun k : A →+* B => k a) hg

end RingHom

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [TopologicalSpace B]

/-- An algebra homomorphism is topologically of finite type when its underlying ring map is. -/
def TopologicallyOfFiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.TopologicallyOfFiniteType

/-- The algebra-homomorphism predicate agrees with the induced ring-homomorphism algebra. -/
theorem topologicallyOfFiniteType_iff (f : A →ₐ[R] B) :
    f.TopologicallyOfFiniteType ↔
      @Algebra.TopologicallyOfFiniteType A B _ _ f.toRingHom.toAlgebra _ :=
  Iff.rfl

end AlgHom
