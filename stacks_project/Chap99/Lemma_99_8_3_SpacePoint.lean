/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.«99_8_1_1_Functor»
public import stacks_project.Chap99.Lemma_99_7_5_SpacePoint

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

/-- A finitely presented quasi-coherent quotient of `F_T` that is flat over an
algebraic space `T` and has support proper over `T`. -/
structure QuotSpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) [FinitePresentation f] where
  /-- The underlying space-level quotient point. -/
  point : SpacePoint f F h
  /-- The target is of finite presentation. -/
  isFinitePresentation : point.module.IsFinitePresentation
  /-- The support of the target is proper over `T`. -/
  hasProperSupport : supportProperOver (pullback.snd f h) point.module

namespace QuotSpacePoint

/-- Construct a space-level Quot-point from an epimorphism `F_T ⟶ Q` with `Q`
quasi-coherent of finite presentation, flat over `T`, and with support proper
over `T`. -/
def ofEpi {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B)
    [FinitePresentation f] (module : (pullback f h).Modules)
    (map : spaceFiberF f F h ⟶ module) (map_epi : Epi map)
    (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f h))
    (isFinitePresentation : module.IsFinitePresentation)
    (hasProperSupport : supportProperOver (pullback.snd f h) module) :
    QuotSpacePoint f F h where
  point := SpacePoint.ofEpi f F h module map map_epi isQuasicoherent isFlat
  isFinitePresentation := isFinitePresentation
  hasProperSupport := hasProperSupport

/-- A space-level Quot-point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
of finite presentation, flat over `T`, and with support proper over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    [FinitePresentation f] (Q : QuotSpacePoint f F h) :
    Epi Q.point.map ∧ Q.point.module.IsQuasicoherent ∧
      Q.point.module.IsFinitePresentation ∧
      Modules.flatOver Q.point.module (pullback.snd f h) ∧
      supportProperOver (pullback.snd f h) Q.point.module :=
  sorry

/-- Pull back a space-level Quot-point along a morphism of algebraic spaces. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    [FinitePresentation f] (Q : QuotSpacePoint f F h) (a : T' ⟶ T) :
    QuotSpacePoint f F (a ≫ h) where
  point := Q.point.pullback a
  isFinitePresentation := sorry
  hasProperSupport := sorry

/-- The module of a pulled-back space-level Quot-point is the module pullback
along `spaceFiberMap`. -/
theorem pullback_module {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} [FinitePresentation f] (Q : QuotSpacePoint f F h) (a : T' ⟶ T) :
    (Q.pullback a).point.module =
      (Modules.pullback (spaceFiberMap f h a)).obj Q.point.module :=
  sorry

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
    Q.toFpSpacePoint.point = Q.point :=
  sorry

end QuotSpacePoint

/-- View a scheme-level Quot-point as a space-level Quot-point along `σ.hom`. -/
def QuotPoint.toQuotSpacePoint {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    QuotSpacePoint f F σ.hom where
  point := Q.point.toSpacePoint
  isFinitePresentation := Q.isFinitePresentation
  hasProperSupport := Q.hasProperSupport

/-- The module of `QuotPoint.toQuotSpacePoint Q` is the underlying module of
`Q`. -/
theorem QuotPoint.toQuotSpacePoint_module {f : X ⟶ B} {F : X.Modules}
    {σ : SchemesOver B} [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toQuotSpacePoint.point.module = Q.point.module :=
  sorry

/-- The quotient map of `QuotPoint.toQuotSpacePoint Q` is the underlying map of
`Q`. -/
theorem QuotPoint.toQuotSpacePoint_map {f : X ⟶ B} {F : X.Modules}
    {σ : SchemesOver B} [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toQuotSpacePoint.point.map = Q.point.map :=
  sorry

/-- Kernel identification is an equivalence relation on space-level Quot-points. -/
theorem quotSpaceSetoid_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) :
    Equivalence (fun Q₁ Q₂ : QuotSpacePoint f F h ↦ SpacePoint.Rel Q₁.point Q₂.point) :=
  sorry

/-- The setoid of space-level Quot-points modulo kernel equality. -/
def quotSpaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) (h : T ⟶ B) : Setoid (QuotSpacePoint f F h) where
  r Q₁ Q₂ := SpacePoint.Rel Q₁.point Q₂.point
  iseqv := quotSpaceSetoid_isEquivalence f F h

/-- Pullback preserves the relation of the space-level Quot setoid. -/
theorem quotSpaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : QuotSpacePoint f F h),
      (quotSpaceSetoid f F h).r Q₁ Q₂ →
        (quotSpaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) :=
  sorry

/-- Kernel identification of space-level Quot-points is preserved by
`toFpSpacePoint`. -/
theorem toFpSpacePoint_rel {T : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] (F : X.Modules) (h : T ⟶ B) :
    ∀ (Q₁ Q₂ : QuotSpacePoint f F h),
      (quotSpaceSetoid f F h).r Q₁ Q₂ →
        (fpSpaceSetoid f F h).r Q₁.toFpSpacePoint Q₂.toFpSpacePoint :=
  sorry

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
    (a : T' ⟶ T) : (Q.pullback a).hom = a ≫ Q.hom :=
  sorry

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
