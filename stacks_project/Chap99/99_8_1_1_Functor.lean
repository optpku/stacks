module

public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# The Grothendieck Quot functor on algebraic spaces

This module constructs the contravariant functor of finitely presented
quasi-coherent quotients of a quasi-coherent module on an algebraic space,
identified by kernels, required to be flat over the test scheme, and with
support proper over the test scheme.

The proper-support condition is the closed-subspace unfolding of
`Modules.HasProperSupportOver`; that class cannot be imported here together
with `Quot.functor` because `Lemma_67_31_3_FlatOver` and
`Proposition_66_32_1_Comparison` independently declare `schemeEtaleRingedHom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A module on `Y` has proper support over `g : Y ⟶ Z` when some closed
subspace containing the module support is proper over `Z`. -/
def supportProperOver {Y Z : AlgebraicSpace S} (g : Y ⟶ Z) (F : Y.Modules) : Prop :=
  ∃ W : ClosedSubspace Y, Proper (W.ι ≫ g) ∧ Modules.moduleSupport F ⊆ W.pointsSet

/-- Proper support over `g` means some closed subspace containing the module
support is proper over the target. -/
theorem supportProperOver_iff {Y Z : AlgebraicSpace S} (g : Y ⟶ Z) (F : Y.Modules) :
    supportProperOver g F ↔
      ∃ W : ClosedSubspace Y, Proper (W.ι ≫ g) ∧ Modules.moduleSupport F ⊆ W.pointsSet :=
  sorry

/-- A finitely presented quasi-coherent quotient of `F_T` that is flat over `T`
and has support proper over `T`. -/
structure QuotPoint (f : X ⟶ B) (F : X.Modules) (σ : SchemesOver B)
    [FinitePresentation f] where
  /-- The underlying kernel-identified quotient point of `Q_{F/X/B}`. -/
  point : Point f F σ
  /-- The target is of finite presentation. -/
  isFinitePresentation : point.module.IsFinitePresentation
  /-- The support of the target is proper over `T`. -/
  hasProperSupport : supportProperOver (pullback.snd f σ.hom) point.module

namespace QuotPoint

/-- Construct a Quot-point from an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
of finite presentation, flat over `T`, and with support proper over `T`. -/
def ofEpi (f : X ⟶ B) (F : X.Modules) (σ : SchemesOver B)
    [FinitePresentation f] (module : (fiber f σ).Modules)
    (map : fiberF f F σ ⟶ module) (map_epi : Epi map)
    (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f σ.hom))
    (isFinitePresentation : module.IsFinitePresentation)
    (hasProperSupport : supportProperOver (pullback.snd f σ.hom) module) :
    QuotPoint f F σ where
  point := Point.ofEpi f F σ module map map_epi isQuasicoherent isFlat
  isFinitePresentation := isFinitePresentation
  hasProperSupport := hasProperSupport

/-- The underlying `Q_{F/X/B}`-point of a Quot-point. -/
abbrev toPoint {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : Point f F σ :=
  Q.point

/-- A Quot-point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent of finite
presentation, flat over `T`, and with support proper over `T`. -/
theorem spec {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Epi Q.point.map ∧ Q.point.module.IsQuasicoherent ∧
      Q.point.module.IsFinitePresentation ∧
      Modules.flatOver Q.point.module (pullback.snd f σ.hom) ∧
      supportProperOver (pullback.snd f σ.hom) Q.point.module :=
  sorry

/-- Pull back a Quot-point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (h : τ ⟶ σ) :
    QuotPoint f F τ where
  point := Q.point.pullback h
  isFinitePresentation := sorry
  hasProperSupport := sorry

/-- The module of a pulled-back Quot-point is the module pullback along
`fiberMap`. -/
theorem pullback_module {f : X ⟶ B} {F : X.Modules} {σ τ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).point.module =
      (Modules.pullback (fiberMap f h)).obj Q.point.module := sorry

end QuotPoint

/-- Kernel identification is an equivalence relation on Quot-points. -/
theorem quotSetoid_isEquivalence (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) (σ : SchemesOver B) :
    Equivalence (fun Q₁ Q₂ : QuotPoint f F σ ↦ Rel Q₁.point Q₂.point) := sorry

/-- The setoid of Quot-points modulo kernel equality. -/
def quotSetoid (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : SchemesOver B) : Setoid (QuotPoint f F σ) where
  r Q₁ Q₂ := Rel Q₁.point Q₂.point
  iseqv := quotSetoid_isEquivalence f F σ

/-- Pullback preserves the relation of the Quot setoid. -/
theorem quotSetoid_rel_pullback (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) {σ τ : SchemesOver B} (h : τ ⟶ σ) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (quotSetoid f F τ).r (Q₁.pullback h) (Q₂.pullback h) := sorry

/-- Pullback along the identity induces the identity on kernel-identified
Quot classes. -/
theorem quot_map_id (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : (SchemesOver B)ᵒᵖ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback (𝟙 σ).unop)
        (quotSetoid_rel_pullback f F (𝟙 σ).unop)) =
      𝟙 (_root_.Quotient (quotSetoid f F σ.unop)) := sorry

/-- Pullback along a composite induces the composite of the pullback maps on
Quot classes. -/
theorem quot_map_comp (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    {σ τ ρ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback (h ≫ k).unop)
        (quotSetoid_rel_pullback f F (h ≫ k).unop)) =
      TypeCat.ofHom
          (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback h.unop)
            (quotSetoid_rel_pullback f F h.unop)) ≫
        TypeCat.ofHom
          (_root_.Quotient.map (fun Q : QuotPoint f F τ.unop ↦ Q.pullback k.unop)
            (quotSetoid_rel_pullback f F k.unop)) := sorry

/-- The Grothendieck Quot functor `Quot_{F/X/B}` of finitely presented
quasi-coherent quotients of `F` along a finite-presentation morphism
`f : X ⟶ B`, identified by kernels, flat over the test scheme, and with
support proper over the test scheme. -/
def quot (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (quotSetoid f F σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback h.unop)
        (quotSetoid_rel_pullback f F h.unop))
  map_id := quot_map_id f F
  map_comp := quot_map_comp f F

/-- The value of the Quot functor is the setoid quotient of Quot-points by
kernels. -/
theorem quot_obj (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemesOver B) :
    (quot f F).obj (op σ) = _root_.Quotient (quotSetoid f F σ) := sorry

/-- The Quot functor acts on a morphism by pullback of Quot-points. -/
theorem quot_map (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {σ τ : (SchemesOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (quot f F).map h =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback h.unop)
          (quotSetoid_rel_pullback f F h.unop)) := sorry

/-- The forgetful map from Quot-points to quotient points preserves kernel
identification. -/
theorem toPoint_rel (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (quotientSetoid f F σ).r Q₁.toPoint Q₂.toPoint := sorry

/-- The inclusion of the Quot functor as a subfunctor of `Q_{F/X/B}`. -/
def quotι (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] : quot f F ⟶ functor f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.toPoint)
        (toPoint_rel f F σ.unop))
  naturality := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
