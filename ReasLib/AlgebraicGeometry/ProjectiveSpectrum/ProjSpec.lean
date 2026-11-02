/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Total
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# The Proj--Spec diagram

This file packages the tail model, schemes, morphisms, and relative-spectrum presentations
in the comparison between a nonnegatively graded ring and its tail algebra.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjSpec

/-- The additive tail `A_{≥ d}` of an explicit nonnegatively graded ring. -/
def tail (A : Scheme.Hom.AbsoluteProjModel) (d : ℕ) : Submodule ℤ A.ring :=
  ⨆ n : {n : ℕ // d ≤ n},
    Submodule.span ℤ (@SetLike.coe A.grade A.ring A.gradeSetLike (A.grading n))

/-- The canonical open `Spec(A) ∖ V(A₊)` attached to an explicit graded model. -/
def puncturedSpectrum (A : Scheme.Hom.AbsoluteProjModel) :
    (AlgebraicGeometry.Spec A.ring).Opens :=
  Scheme.Modules.idealComplementOpens
    (@HomogeneousIdeal.toIdeal ℕ A.grade A.ring inferInstance A.gradeSetLike
      A.gradeAddSubgroupClass.toAddSubmonoidClass A.grading inferInstance inferInstance
      A.grading_inst
      (@HomogeneousIdeal.irrelevant ℕ A.grade A.ring inferInstance
        inferInstance inferInstance inferInstance inferInstance A.gradeSetLike
        A.gradeAddSubgroupClass.toAddSubmonoidClass A.grading A.grading_inst))

/-- The morphism `Proj(B) ⟶ Proj(A)` induced by a graded map whose natural domain is all of
`Proj(B)`. -/
def fullProjMap {A B : Scheme.Hom.AbsoluteProjModel}
    (ψ : @GradedRingHom ℕ A.ring B.ring A.grade B.grade inferInstance inferInstance
      A.gradeSetLike B.gradeSetLike A.grading B.grading)
    (hψ :
      @projMapDomain A.ring B.ring A.grade B.grade
        inferInstance A.gradeSetLike A.gradeAddSubgroupClass
        inferInstance B.gradeSetLike B.gradeAddSubgroupClass
        A.grading B.grading A.grading_inst B.grading_inst ψ = ⊤) :
    B.proj ⟶ A.proj :=
  (Scheme.topIso B.proj).inv ≫ (B.proj.isoOfEq hψ.symm).hom ≫
    @projMapMap A.ring B.ring A.grade B.grade
      inferInstance A.gradeSetLike A.gradeAddSubgroupClass
      inferInstance B.gradeSetLike B.gradeAddSubgroupClass
      A.grading B.grading A.grading_inst B.grading_inst ψ

/-- Explicit input data for the Proj--Spec diagram associated to a graded ring `A` and its
tail algebra `B`, with `B_d ≃ A_{≥ d}`. -/
structure Construction where
  /-- The original nonnegatively graded ring model. -/
  A : Scheme.Hom.AbsoluteProjModel
  /-- The tail algebra `B = ⊕ (d : ℕ), A_{≥ d}` with its nonnegative grading. -/
  B : Scheme.Hom.AbsoluteProjModel
  /-- The degree-`d` piece of `B` is the additive tail `A_{≥ d}`. -/
  tailPieceIso : ∀ d : ℕ,
    Submodule.span ℤ (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)) ≃+
      tail A d
  /-- The degreewise tail identifications preserve multiplication in the tail algebra. -/
  tailPieceIso_mul : ∀ (d e : ℕ) (x y : B.ring)
      (hx : x ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)))
      (hy : y ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading e)))
      (hxy : x * y ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading (d + e)))),
    (tailPieceIso (d + e) ⟨x * y, hxy⟩).1 =
      (tailPieceIso d ⟨x, hx⟩).1 * (tailPieceIso e ⟨y, hy⟩).1
  /-- The map `σ : A ⟶ B`, whose image is the degree-zero part of `B`. -/
  σ : A.ring ⟶ B.ring
  /-- The image of `σ` lies in the degree-zero part of the tail algebra. -/
  σ_mem_zero : ∀ a : A.ring,
    σ a ∈ @SetLike.coe B.grade B.ring B.gradeSetLike (B.grading 0)
  /-- Under `B₀ ≃ A_{≥ 0}`, the map `σ` is the canonical copy of `A` in degree zero. -/
  tailPieceIso_σ : ∀ a : A.ring,
    (tailPieceIso 0 ⟨σ a, Submodule.subset_span (σ_mem_zero a)⟩).1 = a
  /-- The graded map `ψ : A ⟶ B`. -/
  ψ : @GradedRingHom ℕ A.ring B.ring A.grade B.grade inferInstance inferInstance
    A.gradeSetLike B.gradeSetLike A.grading B.grading
  /-- On a homogeneous element, `ψ` is the canonical inclusion into the corresponding
  tail piece. -/
  tailPieceIso_ψ : ∀ (d : ℕ) (a : A.ring)
      (ha : a ∈ @SetLike.coe A.grade A.ring A.gradeSetLike (A.grading d)),
    (tailPieceIso d
      ⟨ψ a, Submodule.subset_span
        (@GradedRingHom.map_mem ℕ A.ring B.ring A.grade B.grade
          inferInstance inferInstance A.gradeSetLike B.gradeSetLike
          A.grading B.grading ψ d a ha)⟩).1 = a
  /-- The graded quotient map `τ : B ⟶ A`. -/
  τ : @GradedRingHom ℕ B.ring A.ring B.grade A.grade inferInstance inferInstance
    B.gradeSetLike A.gradeSetLike B.grading A.grading
  /-- On the degree-`d` tail, `τ` takes the degree-`d` component in `A`. -/
  tailPieceIso_τ : ∀ (d : ℕ) (b : B.ring)
      (hb : b ∈ @SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)),
    τ b =
      @GradedRing.proj ℕ A.ring A.grade inferInstance inferInstance
        inferInstance A.gradeSetLike
        A.gradeAddSubgroupClass.toAddSubmonoidClass A.grading A.grading_inst d
        (tailPieceIso d ⟨b, Submodule.subset_span hb⟩).1
  /-- The degree-zero part of `B` is identified with `A` through `σ`. -/
  degreeZeroIso : A.ring ≅ B.degreeZeroRing
  /-- The degree-zero identification followed by inclusion into `B` is `σ`. -/
  degreeZeroIso_hom :
    degreeZeroIso.hom ≫ B.degreeZeroToRing = σ
  /-- The quotient `τ` is a retraction of the graded map `ψ`. -/
  τ_comp_ψ :
    CommRingCat.ofHom
          (@GradedRingHom.toRingHom ℕ A.ring B.ring A.grade B.grade
            inferInstance inferInstance A.gradeSetLike B.gradeSetLike
            A.grading B.grading ψ) ≫
        CommRingCat.ofHom
          (@GradedRingHom.toRingHom ℕ B.ring A.ring B.grade A.grade
            inferInstance inferInstance B.gradeSetLike A.gradeSetLike
            B.grading A.grading τ) =
      𝟙 A.ring
  /-- The natural domain of the Proj map induced by `ψ` is all of `Proj(B)`. -/
  ψ_domain :
    @projMapDomain A.ring B.ring A.grade B.grade
      inferInstance A.gradeSetLike A.gradeAddSubgroupClass
      inferInstance B.gradeSetLike B.gradeAddSubgroupClass
      A.grading B.grading A.grading_inst B.grading_inst ψ = ⊤
  /-- The chosen integral twists on `P = Proj(A)`. -/
  twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
    A.gradeAddSubgroupClass A.grading A.grading_inst
  /-- The explicit integral and nonnegative total twist algebras. -/
  totals : TwistTotals A twists
  /-- A chosen relative spectrum of the integral total twist algebra. -/
  integerSpectrum : Scheme.RelativeSpectrumOver totals.integer
  /-- The integral chosen model satisfies the relative-spectrum universal property. -/
  integerSpectrum_valid : Scheme.IsRelativeSpectrumOver integerSpectrum
  /-- A chosen relative spectrum of the nonnegative total twist algebra. -/
  nonnegativeSpectrum : Scheme.RelativeSpectrumOver totals.nonnegative
  /-- The nonnegative chosen model satisfies the relative-spectrum universal property. -/
  nonnegativeSpectrum_valid : Scheme.IsRelativeSpectrumOver nonnegativeSpectrum
  /-- The restriction `U ⟶ P` of the Proj morphism to the irrelevant-ideal complement. -/
  openToProj : (puncturedSpectrum A).toScheme ⟶ A.proj
  /-- The projectivization map `U ⟶ P` is compatible with the maps from `U` and `P` to
  `Spec(A₀)`. -/
  openToProj_toSpecZero :
    openToProj ≫ A.toSpecZero =
      (puncturedSpectrum A).ι ≫ AlgebraicGeometry.Spec.map A.degreeZeroToRing
  /-- The distinguished morphism `U ⟶ L` obtained by identifying `U` with the inverse
  image of `U ⊆ X` under `L ⟶ X`. -/
  openToTailProj : (puncturedSpectrum A).toScheme ⟶ B.proj
  /-- The distinguished morphism `U ⟶ L` realizes the restriction of `L ⟶ X` over the
  open `U ⊆ X` as an isomorphism. -/
  openToTailProj_isPullback :
    IsPullback openToTailProj (𝟙 (puncturedSpectrum A).toScheme)
      (B.toSpecZero ≫ AlgebraicGeometry.Spec.map degreeZeroIso.hom)
      (puncturedSpectrum A).ι
  /-- The algebra map making `U` the integral relative spectrum over `P`. -/
  openUniversalMap :
    totals.integer.obj ⟶
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap openToProj.toShHom)
  /-- The algebra map making `L = Proj(B)` the nonnegative relative spectrum over `P`. -/
  projUniversalMap :
    totals.nonnegative.obj ⟶
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap
        (fullProjMap ψ ψ_domain).toShHom)
  /-- Pulling the nonnegative-twist point on `L` back along the distinguished `U ⟶ L`
  gives the point induced by the inclusion into the integral total twist algebra. -/
  openToTailProj_point :
    Scheme.relativeSpectrumPairPullbackMap totals.nonnegative openToTailProj
        (⟨fullProjMap ψ ψ_domain, projUniversalMap⟩ :
          Scheme.relativeSpectrumPair totals.nonnegative B.proj) =
      (⟨openToProj,
        (Scheme.QcAlgebraUnder.forget A.proj).map totals.inclusion ≫ openUniversalMap⟩ :
        Scheme.relativeSpectrumPair totals.nonnegative (puncturedSpectrum A).toScheme)
  /-- The integral relative spectrum is identified with `U` as a scheme over `P`. -/
  integerIsoOpen :
    Over.mk integerSpectrum.π ≅ Over.mk openToProj
  /-- Pulling back the universal integral-spectrum point along the chosen identification gives
  the canonical integral-twist point on `U`. -/
  integerIsoOpen_spec :
    Scheme.relativeSpectrumPairPullbackMap totals.integer integerIsoOpen.inv.left
        (Scheme.relativeSpecPoint integerSpectrum) =
      (⟨openToProj, openUniversalMap⟩ :
        Scheme.relativeSpectrumPair totals.integer (puncturedSpectrum A).toScheme)
  /-- The nonnegative relative spectrum is identified with `L = Proj(B)` over `P`. -/
  nonnegativeIsoProj :
    Over.mk nonnegativeSpectrum.π ≅ Over.mk (fullProjMap ψ ψ_domain)
  /-- Pulling back the universal nonnegative-spectrum point along the chosen identification
  gives the canonical nonnegative-twist point on `L`. -/
  nonnegativeIsoProj_spec :
    Scheme.relativeSpectrumPairPullbackMap totals.nonnegative
        nonnegativeIsoProj.inv.left (Scheme.relativeSpecPoint nonnegativeSpectrum) =
      (⟨fullProjMap ψ ψ_domain, projUniversalMap⟩ :
        Scheme.relativeSpectrumPair totals.nonnegative B.proj)

namespace Construction

/-- Construct the explicit input to the Proj--Spec diagram from the two graded models, their
ring maps, total twist algebras, relative spectra, and comparison morphisms. -/
def of (A B : Scheme.Hom.AbsoluteProjModel)
    (tailPieceIso : ∀ d : ℕ,
      Submodule.span ℤ (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)) ≃+
        tail A d)
    (tailPieceIso_mul : ∀ (d e : ℕ) (x y : B.ring)
      (hx : x ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)))
      (hy : y ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading e)))
      (hxy : x * y ∈ Submodule.span ℤ
        (@SetLike.coe B.grade B.ring B.gradeSetLike (B.grading (d + e)))),
      (tailPieceIso (d + e) ⟨x * y, hxy⟩).1 =
        (tailPieceIso d ⟨x, hx⟩).1 * (tailPieceIso e ⟨y, hy⟩).1)
    (σ : A.ring ⟶ B.ring)
    (σ_mem_zero : ∀ a : A.ring,
      σ a ∈ @SetLike.coe B.grade B.ring B.gradeSetLike (B.grading 0))
    (tailPieceIso_σ : ∀ a : A.ring,
      (tailPieceIso 0 ⟨σ a, Submodule.subset_span (σ_mem_zero a)⟩).1 = a)
    (ψ : @GradedRingHom ℕ A.ring B.ring A.grade B.grade inferInstance inferInstance
      A.gradeSetLike B.gradeSetLike A.grading B.grading)
    (tailPieceIso_ψ : ∀ (d : ℕ) (a : A.ring)
      (ha : a ∈ @SetLike.coe A.grade A.ring A.gradeSetLike (A.grading d)),
      (tailPieceIso d
        ⟨ψ a, Submodule.subset_span
          (@GradedRingHom.map_mem ℕ A.ring B.ring A.grade B.grade
            inferInstance inferInstance A.gradeSetLike B.gradeSetLike
            A.grading B.grading ψ d a ha)⟩).1 = a)
    (τ : @GradedRingHom ℕ B.ring A.ring B.grade A.grade inferInstance inferInstance
      B.gradeSetLike A.gradeSetLike B.grading A.grading)
    (tailPieceIso_τ : ∀ (d : ℕ) (b : B.ring)
      (hb : b ∈ @SetLike.coe B.grade B.ring B.gradeSetLike (B.grading d)),
      τ b =
        @GradedRing.proj ℕ A.ring A.grade inferInstance inferInstance
          inferInstance A.gradeSetLike
          A.gradeAddSubgroupClass.toAddSubmonoidClass A.grading A.grading_inst d
          (tailPieceIso d ⟨b, Submodule.subset_span hb⟩).1)
    (degreeZeroIso : A.ring ≅ B.degreeZeroRing)
    (degreeZeroIso_hom : degreeZeroIso.hom ≫ B.degreeZeroToRing = σ)
    (τ_comp_ψ :
      CommRingCat.ofHom
            (@GradedRingHom.toRingHom ℕ A.ring B.ring A.grade B.grade
              inferInstance inferInstance A.gradeSetLike B.gradeSetLike
              A.grading B.grading ψ) ≫
          CommRingCat.ofHom
            (@GradedRingHom.toRingHom ℕ B.ring A.ring B.grade A.grade
              inferInstance inferInstance B.gradeSetLike A.gradeSetLike
              B.grading A.grading τ) =
        𝟙 A.ring)
    (ψ_domain :
      @projMapDomain A.ring B.ring A.grade B.grade
        inferInstance A.gradeSetLike A.gradeAddSubgroupClass
        inferInstance B.gradeSetLike B.gradeAddSubgroupClass
        A.grading B.grading A.grading_inst B.grading_inst ψ = ⊤)
    (twists : @ProjTwistAlgebra A.ring A.grade A.ring.commRing A.gradeSetLike
      A.gradeAddSubgroupClass A.grading A.grading_inst)
    (totals : TwistTotals A twists)
    (integerSpectrum : Scheme.RelativeSpectrumOver totals.integer)
    (integerSpectrum_valid : Scheme.IsRelativeSpectrumOver integerSpectrum)
    (nonnegativeSpectrum : Scheme.RelativeSpectrumOver totals.nonnegative)
    (nonnegativeSpectrum_valid : Scheme.IsRelativeSpectrumOver nonnegativeSpectrum)
    (openToProj : (puncturedSpectrum A).toScheme ⟶ A.proj)
    (openToProj_toSpecZero :
      openToProj ≫ A.toSpecZero =
        (puncturedSpectrum A).ι ≫ AlgebraicGeometry.Spec.map A.degreeZeroToRing)
    (openToTailProj : (puncturedSpectrum A).toScheme ⟶ B.proj)
    (openToTailProj_isPullback :
      IsPullback openToTailProj (𝟙 (puncturedSpectrum A).toScheme)
        (B.toSpecZero ≫ AlgebraicGeometry.Spec.map degreeZeroIso.hom)
        (puncturedSpectrum A).ι)
    (openUniversalMap :
      totals.integer.obj ⟶
        Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap openToProj.toShHom))
    (projUniversalMap :
      totals.nonnegative.obj ⟶
        Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap
          (fullProjMap ψ ψ_domain).toShHom))
    (openToTailProj_point :
      Scheme.relativeSpectrumPairPullbackMap totals.nonnegative openToTailProj
          (⟨fullProjMap ψ ψ_domain, projUniversalMap⟩ :
            Scheme.relativeSpectrumPair totals.nonnegative B.proj) =
        (⟨openToProj,
          (Scheme.QcAlgebraUnder.forget A.proj).map totals.inclusion ≫ openUniversalMap⟩ :
          Scheme.relativeSpectrumPair totals.nonnegative (puncturedSpectrum A).toScheme))
    (integerIsoOpen : Over.mk integerSpectrum.π ≅ Over.mk openToProj)
    (integerIsoOpen_spec :
      Scheme.relativeSpectrumPairPullbackMap totals.integer integerIsoOpen.inv.left
          (Scheme.relativeSpecPoint integerSpectrum) =
        (⟨openToProj, openUniversalMap⟩ :
          Scheme.relativeSpectrumPair totals.integer (puncturedSpectrum A).toScheme))
    (nonnegativeIsoProj :
      Over.mk nonnegativeSpectrum.π ≅ Over.mk (fullProjMap ψ ψ_domain))
    (nonnegativeIsoProj_spec :
      Scheme.relativeSpectrumPairPullbackMap totals.nonnegative
          nonnegativeIsoProj.inv.left (Scheme.relativeSpecPoint nonnegativeSpectrum) =
        (⟨fullProjMap ψ ψ_domain, projUniversalMap⟩ :
          Scheme.relativeSpectrumPair totals.nonnegative B.proj)) :
    Construction where
  A := A
  B := B
  tailPieceIso := tailPieceIso
  tailPieceIso_mul := tailPieceIso_mul
  σ := σ
  σ_mem_zero := σ_mem_zero
  tailPieceIso_σ := tailPieceIso_σ
  ψ := ψ
  tailPieceIso_ψ := tailPieceIso_ψ
  τ := τ
  tailPieceIso_τ := tailPieceIso_τ
  degreeZeroIso := degreeZeroIso
  degreeZeroIso_hom := degreeZeroIso_hom
  τ_comp_ψ := τ_comp_ψ
  ψ_domain := ψ_domain
  twists := twists
  totals := totals
  integerSpectrum := integerSpectrum
  integerSpectrum_valid := integerSpectrum_valid
  nonnegativeSpectrum := nonnegativeSpectrum
  nonnegativeSpectrum_valid := nonnegativeSpectrum_valid
  openToProj := openToProj
  openToProj_toSpecZero := openToProj_toSpecZero
  openToTailProj := openToTailProj
  openToTailProj_isPullback := openToTailProj_isPullback
  openUniversalMap := openUniversalMap
  projUniversalMap := projUniversalMap
  openToTailProj_point := openToTailProj_point
  integerIsoOpen := integerIsoOpen
  integerIsoOpen_spec := integerIsoOpen_spec
  nonnegativeIsoProj := nonnegativeIsoProj
  nonnegativeIsoProj_spec := nonnegativeIsoProj_spec

/-- The affine scheme `X = Spec(A)`. -/
abbrev X (C : Construction) : Scheme := AlgebraicGeometry.Spec C.A.ring

/-- The closed affine scheme `Z = Spec(A₀)`. -/
abbrev Z (C : Construction) : Scheme := C.A.specZero

/-- The projective scheme `P = Proj(A)`. -/
abbrev P (C : Construction) : Scheme := C.A.proj

/-- The projective scheme `L = Proj(B)`. -/
abbrev L (C : Construction) : Scheme := C.B.proj

/-- The open `U = Spec(A) ∖ V(A₊)`. -/
abbrev U (C : Construction) : C.X.Opens := puncturedSpectrum C.A

/-- The structural morphism `L ⟶ X` induced by `σ : A ≅ B₀`. -/
def σMap (C : Construction) : C.L ⟶ C.X :=
  C.B.toSpecZero ≫ AlgebraicGeometry.Spec.map C.degreeZeroIso.hom

/-- The morphism `π : L ⟶ P` induced by the graded map `ψ`. -/
def π (C : Construction) : C.L ⟶ C.P := fullProjMap C.ψ C.ψ_domain

/-- The affine morphism `X ⟶ Z` induced by the inclusion `A₀ ⟶ A`. -/
def toZero (C : Construction) : C.X ⟶ C.Z :=
  AlgebraicGeometry.Spec.map C.A.degreeZeroToRing

/-- The projective structural morphism `P ⟶ Z`. -/
def projToZero (C : Construction) : C.P ⟶ C.Z := C.A.toSpecZero

/-- The scheme morphism between relative spectra induced contravariantly by the inclusion of
the nonnegative total twist algebra into the integral total twist algebra. -/
def totalMapHom (C : Construction) :
    C.integerSpectrum.scheme ⟶ C.nonnegativeSpectrum.scheme :=
  C.nonnegativeSpectrum_valid.isRepresentedBy.representableBy.homEquiv.symm
    (⟨C.integerSpectrum.π,
      (Scheme.QcAlgebraUnder.forget C.P).map C.totals.inclusion ≫
        C.integerSpectrum.universalMap⟩ :
      Scheme.relativeSpectrumPair C.totals.nonnegative C.integerSpectrum.scheme)

/-- The canonical relative-spectrum morphism pulls the universal nonnegative-twist point back
to the point induced by the inclusion into the integral twist algebra. -/
theorem totalMapHom_spec (C : Construction) :
    Scheme.relativeSpectrumPairPullbackMap C.totals.nonnegative C.totalMapHom
        (Scheme.relativeSpecPoint C.nonnegativeSpectrum) =
      (⟨C.integerSpectrum.π,
        (Scheme.QcAlgebraUnder.forget C.P).map C.totals.inclusion ≫
          C.integerSpectrum.universalMap⟩ :
        Scheme.relativeSpectrumPair C.totals.nonnegative C.integerSpectrum.scheme) := by
  exact C.nonnegativeSpectrum_valid.isRepresentedBy.representableBy.homEquiv.apply_symm_apply _

/-- The canonical relative-spectrum morphism lies over `P`. -/
theorem totalMapHom_over (C : Construction) :
    C.totalMapHom ≫ C.nonnegativeSpectrum.π = C.integerSpectrum.π := by
  exact congrArg Sigma.fst C.totalMapHom_spec

/-- The morphism in `Over P` induced contravariantly by the inclusion of total twist
algebras. -/
def totalMap (C : Construction) :
    Over.mk C.integerSpectrum.π ⟶ Over.mk C.nonnegativeSpectrum.π :=
  Over.homMk C.totalMapHom C.totalMapHom_over

/-- The underlying scheme morphism of `totalMap` is the universal-map construction. -/
theorem totalMap_left (C : Construction) : C.totalMap.left = C.totalMapHom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transporting the relative-spectrum morphism through the two canonical identifications gives
the distinguished morphism `U ⟶ L`. -/
theorem totalMap_transport (C : Construction) :
    C.totalMap.left ≫ C.nonnegativeIsoProj.hom.left =
      C.integerIsoOpen.hom.left ≫ C.openToTailProj := by
  rw [totalMap_left]
  apply (cancel_epi C.integerIsoOpen.inv.left).mp
  apply (cancel_mono C.nonnegativeIsoProj.inv.left).mp
  have hi : C.integerIsoOpen.inv.left ≫ C.integerIsoOpen.hom.left = 𝟙 _ :=
    congrArg Over.Hom.left C.integerIsoOpen.inv_hom_id
  have hn : C.nonnegativeIsoProj.hom.left ≫ C.nonnegativeIsoProj.inv.left = 𝟙 _ :=
    congrArg Over.Hom.left C.nonnegativeIsoProj.hom_inv_id
  simp only [Category.assoc, hn, Category.comp_id, reassoc_of% hi]
  apply C.nonnegativeSpectrum_valid.isRepresentedBy.map_bijective.injective
  change Scheme.relativeSpectrumPairPullbackMap C.totals.nonnegative
      (C.integerIsoOpen.inv.left ≫ C.totalMapHom) _ =
    Scheme.relativeSpectrumPairPullbackMap C.totals.nonnegative
      (C.openToTailProj ≫ C.nonnegativeIsoProj.inv.left) _
  have hcomp {S T T' T'' : Scheme} (A : S.QcAlgebraUnder)
      (a : T'' ⟶ T') (b : T' ⟶ T) (x : Scheme.relativeSpectrumPair A T) :
      Scheme.relativeSpectrumPairPullbackMap A (a ≫ b) x =
        Scheme.relativeSpectrumPairPullbackMap A a
          (Scheme.relativeSpectrumPairPullbackMap A b x) := by
    rfl
  rw [hcomp, hcomp, C.totalMapHom_spec, C.nonnegativeIsoProj_spec,
    C.openToTailProj_point]
  simpa only [Scheme.relativeSpectrumPairPullbackMap, Scheme.relativeSpectrumFunctorMap,
    Scheme.relativeSpecPoint, Scheme.RelativeSpectrumOver.point, P, U, Over.mk_left,
    Category.assoc] using
    congrArg (fun x : Scheme.relativeSpectrumPair C.totals.integer C.U.toScheme ↦
      (⟨x.1, (Scheme.QcAlgebraUnder.forget C.P).map C.totals.inclusion ≫ x.2⟩ :
        Scheme.relativeSpectrumPair C.totals.nonnegative C.U.toScheme))
      C.integerIsoOpen_spec

set_option backward.isDefEq.respectTransparency false in
/-- The left square of the Proj--Spec diagram commutes. -/
theorem left_comm (C : Construction) :
    C.totalMap.left ≫ C.nonnegativeIsoProj.hom.left ≫ C.σMap =
      C.integerIsoOpen.hom.left ≫ C.U.ι := by
  rw [← Category.assoc, C.totalMap_transport, Category.assoc]
  simpa only [σMap, U, Category.id_comp] using
    congrArg (C.integerIsoOpen.hom.left ≫ ·) C.openToTailProj_isPullback.w

set_option backward.isDefEq.respectTransparency false in
/-- The right square of the Proj--Spec diagram commutes. -/
theorem right_comm (C : Construction) :
    C.nonnegativeIsoProj.hom.left ≫ C.σMap ≫ C.toZero =
      C.nonnegativeSpectrum.π ≫ C.projToZero := by
  letI := C.A.gradeSetLike
  letI := C.A.gradeAddSubgroupClass
  letI := C.A.grading_inst
  letI := C.B.gradeSetLike
  letI := C.B.gradeAddSubgroupClass
  letI := C.B.grading_inst
  let φ : C.A.degreeZeroRing ⟶ C.B.degreeZeroRing :=
    C.A.degreeZeroToRing ≫ C.degreeZeroIso.hom
  have hφ (a : C.A.degreeZeroRing) : (φ a).1 = C.ψ a.1 := by
    have hs := congrArg (fun f : C.A.ring ⟶ C.B.ring ↦ f a.1) C.degreeZeroIso_hom
    change (φ a).1 = C.σ a.1 at hs
    rw [hs]
    symm
    exact congrArg Subtype.val ((C.tailPieceIso 0).injective
      (Subtype.ext ((C.tailPieceIso_ψ 0 a.1 a.2).trans (C.tailPieceIso_σ a.1).symm)))
  have hdom : projMapMap C.ψ ≫ Proj.toSpecZero C.A.grading =
      (projMapDomain C.ψ).ι ≫ Proj.toSpecZero C.B.grading ≫ Spec.map φ := by
    apply (projMapOpenCover C.ψ).hom_ext
    intro f
    change PositiveHomogeneous C.A.grading at f
    dsimp only [projMapMap]
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    change projMapBasicOpenMap C.ψ f ≫ Proj.toSpecZero C.A.grading =
      C.B.proj.homOfLE (basicOpen_le_projMapDomain C.ψ f.degree_pos f.mem_degree) ≫
        (projMapDomain C.ψ).ι ≫ Proj.toSpecZero C.B.grading ≫ Spec.map φ
    rw [Scheme.homOfLE_ι_assoc]
    apply (cancel_epi
      (Proj.basicOpenIsoSpec C.B.grading (C.ψ f.val) (C.ψ.map_mem f.mem_degree)
        f.degree_pos).inv).mp
    simp only [projMapBasicOpenMap, Category.assoc, Iso.inv_hom_id_assoc,
      Proj.awayι_toSpecZero, Proj.basicOpenIsoSpec_inv_ι_assoc,
      Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
      HomogeneousLocalization.map_mk]
    exact congrArg (fun b : C.B.ring ↦
      Localization.mk b (1 : Submonoid.powers (C.ψ f.val))) (hφ a).symm
  have hnat : C.π ≫ C.projToZero = C.σMap ≫ C.toZero := by
    change fullProjMap C.ψ C.ψ_domain ≫ Proj.toSpecZero C.A.grading =
      Proj.toSpecZero C.B.grading ≫ Spec.map C.degreeZeroIso.hom ≫
        Spec.map C.A.degreeZeroToRing
    rw [← Spec.map_comp]
    change fullProjMap C.ψ C.ψ_domain ≫ Proj.toSpecZero C.A.grading =
      Proj.toSpecZero C.B.grading ≫ Spec.map φ
    simp only [fullProjMap, Category.assoc]
    rw [hdom]
    rw [Scheme.isoOfEq_hom_ι_assoc, ← Category.assoc, Scheme.toIso_inv_ι,
      Category.id_comp]
  rw [← hnat]
  simpa only [π, Over.mk_hom, ← Category.assoc] using
    congrArg (· ≫ C.projToZero) (Over.w C.nonnegativeIsoProj.hom)

end Construction

/-- The bundled two-square diagram identifying the two relative spectra with `U` and `L`. -/
structure Diagram (C : Construction) where
  /-- The top-left horizontal morphism between the two relative spectra over `P`. -/
  top : Over.mk C.integerSpectrum.π ⟶ Over.mk C.nonnegativeSpectrum.π
  /-- The integral relative spectrum is `U` over `P`. -/
  integerIsoOpen : Over.mk C.integerSpectrum.π ≅ Over.mk C.openToProj
  /-- The nonnegative relative spectrum is `L` over `P`. -/
  nonnegativeIsoProj :
    Over.mk C.nonnegativeSpectrum.π ≅ Over.mk C.π
  /-- The square with bottom row `U ⟶ X` commutes. -/
  left_comm :
    top.left ≫ nonnegativeIsoProj.hom.left ≫ C.σMap =
      integerIsoOpen.hom.left ≫ C.U.ι
  /-- The square with bottom row `X ⟶ Z` commutes. -/
  right_comm :
    nonnegativeIsoProj.hom.left ≫ C.σMap ≫ C.toZero =
      C.nonnegativeSpectrum.π ≫ C.projToZero

namespace Diagram

/-- Construct a Proj--Spec diagram from its explicit arrows, identifications, and two square
laws. -/
def of (C : Construction)
    (top : Over.mk C.integerSpectrum.π ⟶ Over.mk C.nonnegativeSpectrum.π)
    (integerIsoOpen : Over.mk C.integerSpectrum.π ≅ Over.mk C.openToProj)
    (nonnegativeIsoProj : Over.mk C.nonnegativeSpectrum.π ≅ Over.mk C.π)
    (left_comm :
      top.left ≫ nonnegativeIsoProj.hom.left ≫ C.σMap =
        integerIsoOpen.hom.left ≫ C.U.ι)
    (right_comm :
      nonnegativeIsoProj.hom.left ≫ C.σMap ≫ C.toZero =
        C.nonnegativeSpectrum.π ≫ C.projToZero) : Diagram C where
  top := top
  integerIsoOpen := integerIsoOpen
  nonnegativeIsoProj := nonnegativeIsoProj
  left_comm := left_comm
  right_comm := right_comm

/-- The two commutative-square equations carried by a Proj--Spec diagram. -/
theorem spec (C : Construction) (D : Diagram C) :
    (D.top.left ≫ D.nonnegativeIsoProj.hom.left ≫ C.σMap =
      D.integerIsoOpen.hom.left ≫ C.U.ι) ∧
    (D.nonnegativeIsoProj.hom.left ≫ C.σMap ≫ C.toZero =
      C.nonnegativeSpectrum.π ≫ C.projToZero) :=
  ⟨D.left_comm, D.right_comm⟩

end Diagram

/-- The canonical bundled Proj--Spec diagram assembled from explicit construction data. -/
def diagram (C : Construction) : Diagram C where
  top := C.totalMap
  integerIsoOpen := C.integerIsoOpen
  nonnegativeIsoProj := C.nonnegativeIsoProj
  left_comm := C.left_comm
  right_comm := C.right_comm

end AlgebraicGeometry.ProjSpec

