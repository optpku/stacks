/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Open

variable {S : Scheme.{u}} {Y V : AlgebraicSpace S}

/-- An open subspace is scheme-theoretically dense if its pullback to every étale scheme
chart, in every scheme representation of that pullback, is scheme-theoretically dominant. -/
def IsSchemeTheoreticallyDense (ι : V ⟶ Y) : Prop :=
  ∀ (U : SmallEtale.site Y) (W : Over S) (map : W ⟶ U.left)
    (toOpen : yoneda.obj W ⟶ V.functorOfPoints),
    IsPullback toOpen (yoneda.map map) (ι : V.functorOfPoints ⟶ Y.functorOfPoints) U.hom →
      AlgebraicGeometry.IsSchemeTheoreticallyDominant map.left

/-- Scheme-theoretic density is equivalent to scheme-theoretic dominance in each genuine
scheme pullback along an étale chart. -/
theorem isSchemeTheoreticallyDense_iff (ι : V ⟶ Y) :
    IsSchemeTheoreticallyDense ι ↔
      ∀ (U : SmallEtale.site Y) (W : Over S) (map : W ⟶ U.left)
        (toOpen : yoneda.obj W ⟶ V.functorOfPoints),
        IsPullback toOpen (yoneda.map map) (ι : V.functorOfPoints ⟶ Y.functorOfPoints) U.hom →
          AlgebraicGeometry.IsSchemeTheoreticallyDominant map.left := Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Open

namespace AlgebraicGeometry.AlgebraicSpace

namespace SchemeTheoreticDensity

variable {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- For every étale morphism `φ : V ⟶ X` of algebraic spaces, the scheme-theoretic
closure of `openInverseImage φ ι` in `V` equals `V`. -/
def forallEtale : Prop :=
  ∀ {V : AlgebraicSpace S} (φ : V ⟶ X),
    Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι)

/-- `forallEtale ι` means every étale preimage of `ι` is scheme-theoretically
dominant into its source. -/
theorem forallEtale_iff : forallEtale ι ↔
    ∀ (V : AlgebraicSpace S) (φ : V ⟶ X),
      Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := by
  constructor
  · intro h V φ hφ
    exact h φ hφ
  · intro h V φ hφ
    exact h V φ hφ

namespace forallEtale

/-- A universal étale-preimage dominance condition witnesses `forallEtale ι`. -/
theorem of (h : ∀ {V : AlgebraicSpace S} (φ : V ⟶ X),
    Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι)) :
    forallEtale ι := h

/-- Under `forallEtale ι`, the open inverse-image inclusion along any étale
morphism to `X` is scheme-theoretically dominant. -/
theorem spec (h : forallEtale ι) {V : AlgebraicSpace S} (φ : V ⟶ X)
    (hφ : Etale φ) : IsSchemeTheoreticallyDominant (openInverseImageι φ ι) :=
  h φ hφ

end forallEtale

/-- There is a scheme `V` over `S` and a surjective étale morphism `φ` from
`ofOver V` to `X` whose open inverse-image inclusion is scheme-theoretically
dominant. -/
def existsSurjectiveEtale : Prop :=
  ∃ (V : Over S) (φ : ofOver V ⟶ X),
    Etale φ ∧ Surjective φ ∧ IsSchemeTheoreticallyDominant (openInverseImageι φ ι)

/-- `existsSurjectiveEtale ι` is the existence of a surjective étale scheme atlas
of `X` along which the open inverse image of `ι` is scheme-theoretically
dominant. -/
theorem existsSurjectiveEtale_iff : existsSurjectiveEtale ι ↔
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := Iff.rfl

namespace existsSurjectiveEtale

/-- A surjective étale scheme atlas of `X` along which the open inverse image of
`ι` is scheme-theoretically dominant witnesses `existsSurjectiveEtale ι`. -/
theorem of {V : Over S} (φ : ofOver V ⟶ X) [Etale φ] [Surjective φ]
    (h : IsSchemeTheoreticallyDominant (openInverseImageι φ ι)) :
    existsSurjectiveEtale ι := ⟨V, φ, inferInstance, inferInstance, h⟩

/-- `existsSurjectiveEtale ι` supplies a surjective étale scheme atlas of `X`
along which the open inverse image of `ι` is scheme-theoretically dominant. -/
theorem spec (h : existsSurjectiveEtale ι) :
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := h

end existsSurjectiveEtale

/-- For an open immersion, scheme-theoretic dominance after every étale base change is
equivalent to scheme-theoretic dominance after one surjective étale scheme atlas. -/
theorem forallEtale_iff_existsSurjectiveEtale :
    forallEtale ι ↔ existsSurjectiveEtale ι := sorry

/-- The universal étale and surjective étale scheme-atlas tests for an open immersion are
mutually equivalent. -/
theorem tfae : List.TFAE [forallEtale ι, existsSurjectiveEtale ι] :=
  List.tfae_cons_cons.mpr
    ⟨forallEtale_iff_existsSurjectiveEtale ι, List.tfae_singleton _⟩

end SchemeTheoreticDensity

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Open

/-- For an open immersion, dominance on every étale scheme chart is equivalent to
scheme-theoretic dominance after every étale algebraic-space base change. -/
theorem isSchemeTheoreticallyDense_iff_forallEtale {S : Scheme.{u}}
    {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ SchemeTheoreticDensity.forallEtale ι := sorry

end AlgebraicGeometry.AlgebraicSpace.Open

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inference-facing form of scheme-theoretic density of an open immersion is
the fact that its pullbacks to all étale scheme charts are scheme-theoretically dominant. -/
abbrev IsSchemeTheoreticallyDense {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] : Prop :=
  Fact (Open.IsSchemeTheoreticallyDense ι)

/-- Scheme-theoretic density of an open immersion is equivalent to dominance
after every étale algebraic-space base change. -/
theorem isSchemeTheoreticallyDense_iff {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ SchemeTheoreticDensity.forallEtale ι :=
  fact_iff.trans (Open.isSchemeTheoreticallyDense_iff_forallEtale ι)

namespace IsSchemeTheoreticallyDense

/-- An open immersion that is an isomorphism is scheme-theoretically dense. -/
@[instance]
theorem of_isIso {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsIso ι] : IsSchemeTheoreticallyDense ι := sorry

/-- The identity morphism of an algebraic space is scheme-theoretically dense. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsSchemeTheoreticallyDense (𝟙 X) := of_isIso (𝟙 X)

/-- The universal étale-preimage dominance test witnesses scheme-theoretic density. -/
theorem of {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
    [IsOpenImmersion ι] (h : SchemeTheoreticDensity.forallEtale ι) :
    IsSchemeTheoreticallyDense ι :=
  (isSchemeTheoreticallyDense_iff ι).mpr h

/-- A scheme-theoretically dense open immersion satisfies the universal
étale-preimage dominance test. -/
theorem spec {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι] :
    SchemeTheoreticDensity.forallEtale ι :=
  (isSchemeTheoreticallyDense_iff ι).mp inferInstance

/-- Every étale preimage of a scheme-theoretically dense open immersion is
scheme-theoretically dominant into its source. -/
theorem forallEtale {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
    [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι] :
    SchemeTheoreticDensity.forallEtale ι := spec ι

/-- Scheme-theoretic density of an open immersion is equivalent to the existence
of a surjective étale scheme atlas along which the open inverse image is
scheme-theoretically dominant. -/
theorem iff_existsSurjectiveEtale {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔ SchemeTheoreticDensity.existsSurjectiveEtale ι :=
  (isSchemeTheoreticallyDense_iff ι).trans
    (SchemeTheoreticDensity.forallEtale_iff_existsSurjectiveEtale ι)

/-- A quasi-compact open immersion of algebraic spaces is scheme-theoretically dense
if and only if it is scheme-theoretically dominant. -/
theorem iff_isSchemeTheoreticallyDominant {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] [QuasiCompact ι] :
    IsSchemeTheoreticallyDense ι ↔ IsSchemeTheoreticallyDominant ι :=
  sorry

/-- Scheme-theoretic dominance of a quasi-compact open immersion implies
scheme-theoretic density. -/
theorem of_isSchemeTheoreticallyDominant {S : Scheme.{u}} {X U : AlgebraicSpace S}
    {ι : U ⟶ X} [IsOpenImmersion ι] [QuasiCompact ι]
    (h : IsSchemeTheoreticallyDominant ι) : IsSchemeTheoreticallyDense ι :=
  (iff_isSchemeTheoreticallyDominant ι).mpr h

/-- A scheme-theoretically dense quasi-compact open immersion is
scheme-theoretically dominant. -/
instance instIsSchemeTheoreticallyDominant {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] [QuasiCompact ι]
    [IsSchemeTheoreticallyDense ι] : IsSchemeTheoreticallyDominant ι :=
  (iff_isSchemeTheoreticallyDominant ι).mp inferInstance

end IsSchemeTheoreticallyDense

end AlgebraicGeometry.AlgebraicSpace
