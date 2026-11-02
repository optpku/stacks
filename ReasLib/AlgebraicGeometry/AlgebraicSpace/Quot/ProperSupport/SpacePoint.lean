/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.SpacePoint

/-!
# Space-level Quot points of a quasi-coherent module

This module extends the scheme-level Quot-points of `Quot_{F/X/B}` to an
algebraic space `T` over `S`, via a morphism `h : T ⟶ B` and a
kernel-identified finitely presented `T`-flat quotient of the pullback of `F`
to `X ×_{B,h} T` whose support is proper over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace QuotSpacePoint

/-- Forget proper support, sending a space-level Quot-point to the underlying
finitely presented space-level quotient point of `Q^{fp}_{F/X/B}`. -/
def toFpSpacePoint {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} [FinitePresentation f] (Q : QuotSpacePoint f F h) :
    FpSpacePoint f F h where
  point := Q.point
  isFinitePresentation := Q.isFinitePresentation

/-- `toFpSpacePoint` keeps the same underlying space-level quotient point. -/
theorem toFpSpacePoint_spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} [FinitePresentation f] (Q : QuotSpacePoint f F h) :
    Q.toFpSpacePoint.point = Q.point := sorry

end QuotSpacePoint

/-- The module of `QuotPoint.toQuotSpacePoint Q` is the underlying module of
`Q`. -/
theorem QuotPoint.toQuotSpacePoint_module {f : X ⟶ B} {F : X.Modules}
    {σ : SchemeOver B} [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toQuotSpacePoint.point.module = Q.point.module := rfl

/-- The quotient map of `QuotPoint.toQuotSpacePoint Q` is the underlying map of
`Q`. -/
theorem QuotPoint.toQuotSpacePoint_map {f : X ⟶ B} {F : X.Modules}
    {σ : SchemeOver B} [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toQuotSpacePoint.point.map = Q.point.map := rfl

set_option maxHeartbeats 1000000 in
/-- Proper-support scheme pullback uses the same data as pullback over `B`. -/
theorem QuotPoint.toQuotSpacePoint_pullback {f : X ⟶ B} {F : X.Modules}
    {σ τ : SchemeOver B} [FinitePresentation f] (Q : QuotPoint f F σ) (h : τ ⟶ σ) :
    (QuotPoint.pullback Q h).toQuotSpacePoint =
      Q.toQuotSpacePoint.pullbackOver (h' := τ.hom) ((ofOverFunctor S).map h.left) (CostructuredArrow.w h) := rfl

/-- Kernel identification is an equivalence relation on space-level Quot-points. -/
theorem quotSpaceSetoid_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) :
    Equivalence (fun Q₁ Q₂ : QuotSpacePoint f F h ↦ SpacePoint.Rel Q₁.point Q₂.point) := sorry

/-- The setoid of space-level Quot-points modulo kernel equality. -/
def quotSpaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) (h : T ⟶ B) : Setoid (QuotSpacePoint f F h) where
  r Q₁ Q₂ := SpacePoint.Rel Q₁.point Q₂.point
  iseqv := quotSpaceSetoid_isEquivalence f F h

set_option maxHeartbeats 1000000 in
/-- Pullback preserves the relation of the space-level Quot setoid. -/
theorem quotSpaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : QuotSpacePoint f F h),
      (quotSpaceSetoid f F h).r Q₁ Q₂ →
        (quotSpaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) := sorry

/-- Kernel identification of space-level Quot-points is preserved by
`toFpSpacePoint`. -/
theorem toFpSpacePoint_rel {T : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) :
    ∀ (Q₁ Q₂ : QuotSpacePoint f F h),
      (quotSpaceSetoid f F h).r Q₁ Q₂ →
        (fpSpaceSetoid f F h).r Q₁.toFpSpacePoint Q₂.toFpSpacePoint := sorry

/-- A pair `(h, Q)` consisting of a morphism `h : T ⟶ B` and a kernel-identified
finitely presented quasi-coherent quotient of `F_T` that is flat over `T` and
has support proper over `T`. -/
structure QuotSpaceQuotient (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The kernel-identified finitely presented proper-support quotient class of
  `F_T`. -/
  quotient : _root_.Quotient (quotSpaceSetoid f F hom)

namespace QuotSpaceQuotient

/-- Package a space-level Quot-point over `h : T ⟶ B` as the pair `(h, [Q])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {h : T ⟶ B} (Q : QuotSpacePoint f F h) : QuotSpaceQuotient f F T where
  hom := h
  quotient := Quotient.mk (quotSpaceSetoid f F h) Q

/-- Every proper-support quotient pair has a representative epimorphism with
quasi-coherent finitely presented target, flat over the base and with proper support. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} (Q : QuotSpaceQuotient f F T) :
    ∃ P : QuotSpacePoint f F Q.hom,
      Quotient.mk (quotSpaceSetoid f F Q.hom) P = Q.quotient ∧
        Epi P.point.map ∧ P.point.module.IsQuasicoherent ∧
        P.point.module.IsFinitePresentation ∧
        Modules.flatOver P.point.module (pullback.snd f Q.hom) ∧
        supportProperOver (pullback.snd f Q.hom) P.point.module := sorry

/-- Pull back a space-level Quot pair `(h, Q)` along `a : T' ⟶ T`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} (Q : QuotSpaceQuotient f F T) (a : T' ⟶ T) :
    QuotSpaceQuotient f F T' where
  hom := a ≫ Q.hom
  quotient :=
    _root_.Quotient.map (fun P : QuotSpacePoint f F Q.hom ↦ P.pullback a)
      (quotSpaceSetoid_rel_pullback f F Q.hom a) Q.quotient

/-- The morphism of a pulled-back space-level Quot pair is the composite
`a ≫ Q.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B}
    [FinitePresentation f] {F : X.Modules} (Q : QuotSpaceQuotient f F T)
    (a : T' ⟶ T) : (Q.pullback a).hom = a ≫ Q.hom := sorry

/-- Forget proper support, sending a space-level Quot pair to the underlying
finitely presented pair of `Q^{fp}_{F/X/B}`. -/
def toFpSpaceQuotient {T : AlgebraicSpace S} {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} (Q : QuotSpaceQuotient f F T) : FpSpaceQuotient f F T where
  hom := Q.hom
  quotient :=
    _root_.Quotient.map (fun P : QuotSpacePoint f F Q.hom ↦ P.toFpSpacePoint)
      (toFpSpacePoint_rel f F Q.hom) Q.quotient

end QuotSpaceQuotient

end AlgebraicGeometry.AlgebraicSpace.Quot
