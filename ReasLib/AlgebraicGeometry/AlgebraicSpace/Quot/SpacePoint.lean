/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation

/-!
# Space-level quotient points of a quasi-coherent module

This module packages the common quotient points from `Functor` and
`FinitePresentation` into kernel-identified pairs over an algebraic space `T`,
and records compatibility with the scheme-level facades.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The module of `Point.toSpacePoint Q` is the underlying module of `Q`. -/
theorem Point.toSpacePoint_module {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : Point f F σ) : Q.toSpacePoint.module = Q.module := rfl

/-- The quotient map of `Point.toSpacePoint Q` is the underlying map of `Q`. -/
theorem Point.toSpacePoint_map {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q : Point f F σ) : Q.toSpacePoint.map = Q.map := rfl

/-- Scheme and space points use exactly the same kernel relation. -/
theorem Point.toSpacePoint_rel_iff {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    (Q R : Point f F σ) : SpacePoint.Rel Q.toSpacePoint R.toSpacePoint ↔ Rel Q R :=
  Iff.rfl

set_option maxHeartbeats 1000000 in
/-- Scheme pullback is the common pullback over `B`, with the given structure map. -/
theorem Point.toSpacePoint_pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : Point f F σ) (h : τ ⟶ σ) :
    (Point.pullback Q h).toSpacePoint =
      Q.toSpacePoint.pullbackOver (h' := τ.hom) ((ofOverFunctor S).map h.left) (CostructuredArrow.w h) := rfl

set_option maxHeartbeats 1000000 in
/-- Finite-presentation pullback uses the common pullback over `B`. -/
theorem FpPoint.toFpSpacePoint_pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    (Q : FpPoint f F σ) (h : τ ⟶ σ) :
    (FpPoint.pullback Q h).toFpSpacePoint =
      Q.toFpSpacePoint.pullbackOver (h' := τ.hom) ((ofOverFunctor S).map h.left) (CostructuredArrow.w h) := rfl

/-- The setoid of space-level quotient points modulo kernel equality. -/
def spaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    Setoid (SpacePoint f F h) where
  r := SpacePoint.Rel
  iseqv := SpacePoint.rel_isEquivalence f F h

set_option maxHeartbeats 1000000 in
/-- Pullback preserves the relation of the space-level quotient setoid. -/
theorem spaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : SpacePoint f F h),
      (spaceSetoid f F h).r Q₁ Q₂ →
        (spaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) :=
  fun Q R hQ ↦ SpacePoint.rel_pullbackOver Q R hQ a rfl

/-- A pair `(h, Q)` consisting of a morphism `h : T ⟶ B` and a kernel-identified
quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure SpaceQuotient (f : X ⟶ B) (F : X.Modules) (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The kernel-identified quotient class of `F_T`. -/
  quotient : _root_.Quotient (spaceSetoid f F hom)

namespace SpaceQuotient

/-- Package a space-level quotient point over `h : T ⟶ B` as the pair `(h, [Q])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) : SpaceQuotient f F T where
  hom := h
  quotient := Quotient.mk (spaceSetoid f F h) Q

/-- Pull back a pair `(h, Q)` along `a : T' ⟶ T`, sending it to `(h ∘ a, a^* Q)`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : SpaceQuotient f F T) (a : T' ⟶ T) : SpaceQuotient f F T' where
  hom := a ≫ Q.hom
  quotient :=
    _root_.Quotient.map (fun P : SpacePoint f F Q.hom ↦ P.pullback a)
      (spaceSetoid_rel_pullback f F Q.hom a) Q.quotient

/-- The morphism of a pulled-back pair is the composite `a ≫ Q.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : SpaceQuotient f F T) (a : T' ⟶ T) :
    (Q.pullback a).hom = a ≫ Q.hom := sorry

/-- Every quotient pair has a representative in its quotient class whose map is epic
and whose target is quasi-coherent and flat over the base. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : SpaceQuotient f F T) :
    ∃ P : SpacePoint f F Q.hom,
      Quotient.mk (spaceSetoid f F Q.hom) P = Q.quotient ∧
      Epi P.map ∧ P.module.IsQuasicoherent ∧
      Modules.flatOver P.module (pullback.snd f Q.hom) := sorry

end SpaceQuotient

/-- Kernel identification is an equivalence relation on finitely presented space-level
quotient points. -/
theorem fpSpaceSetoid_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) :
    Equivalence (fun Q₁ Q₂ : FpSpacePoint f F h ↦ SpacePoint.Rel Q₁.point Q₂.point) :=
  sorry

/-- The setoid of finitely presented space-level quotient points modulo kernel equality. -/
def fpSpaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    Setoid (FpSpacePoint f F h) where
  r Q₁ Q₂ := SpacePoint.Rel Q₁.point Q₂.point
  iseqv := fpSpaceSetoid_isEquivalence f F h

set_option maxHeartbeats 1000000 in
/-- Pullback preserves the relation of the finitely presented space-level quotient
setoid. -/
theorem fpSpaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    (F : X.Modules) (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : FpSpacePoint f F h),
      (fpSpaceSetoid f F h).r Q₁ Q₂ →
        (fpSpaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) := sorry

/-- A pair `(h, Q)` consisting of a morphism `h : T ⟶ B` and a kernel-identified
finitely presented quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure FpSpaceQuotient (f : X ⟶ B) (F : X.Modules) (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The kernel-identified finitely presented quotient class of `F_T`. -/
  quotient : _root_.Quotient (fpSpaceSetoid f F hom)

namespace FpSpaceQuotient

/-- Package a finitely presented space-level quotient point over `h : T ⟶ B` as the
pair `(h, [Q])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : FpSpacePoint f F h) : FpSpaceQuotient f F T where
  hom := h
  quotient := Quotient.mk (fpSpaceSetoid f F h) Q

/-- Pull back a finitely presented pair `(h, Q)` along `a : T' ⟶ T`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : FpSpaceQuotient f F T) (a : T' ⟶ T) : FpSpaceQuotient f F T' where
  hom := a ≫ Q.hom
  quotient :=
    _root_.Quotient.map (fun P : FpSpacePoint f F Q.hom ↦ P.pullback a)
      (fpSpaceSetoid_rel_pullback f F Q.hom a) Q.quotient

/-- The morphism of a pulled-back finitely presented pair is the composite `a ≫ Q.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : FpSpaceQuotient f F T) (a : T' ⟶ T) :
    (Q.pullback a).hom = a ≫ Q.hom := sorry

/-- Every finitely presented quotient pair has a representative in its quotient class
whose map is epic and whose target is quasi-coherent, finitely presented, and flat over the base. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : FpSpaceQuotient f F T) :
    ∃ P : FpSpacePoint f F Q.hom,
      Quotient.mk (fpSpaceSetoid f F Q.hom) P = Q.quotient ∧
      Epi P.point.map ∧ P.point.module.IsQuasicoherent ∧
      P.point.module.IsFinitePresentation ∧
      Modules.flatOver P.point.module (pullback.snd f Q.hom) := sorry

end FpSpaceQuotient

end AlgebraicGeometry.AlgebraicSpace.Quot
