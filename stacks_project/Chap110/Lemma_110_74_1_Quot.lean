/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap110.Lemma_110_74_1_FormalModule

/-!
# The Quot functor of the non-separated algebraization example

`Quot.quot` from 99.8.1 cannot be imported together with `CohStack.toGroupoids`,
because `Lemma_67_31_3_FlatOver` and `Proposition_66_32_1_Comparison` both
declare `schemeEtaleRingedHom`. This module reconstructs `Quot_{F/X/B}` on
`(Sch/B)ᵒᵖ` from the CohStack fibre and module-pullback API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.NonseparatedAlgebraization

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pullback `F_T` of a module `F` along the projection `X_T ⟶ X`. -/
def fiberF (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) : (fiber f σ).Modules :=
  (Modules.pullback (pullback.fst f σ.hom)).obj F

/-- Unfolding of `fiberF`. -/
theorem fiberF_eq (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) :
    fiberF f F σ = (Modules.pullback (pullback.fst f σ.hom)).obj F :=
  sorry

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `X_{T'} ⟶ X_T`. -/
def fiberFCompIso (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    fiberF f F τ ≅ (Modules.pullback (fiberMap f h)).obj (fiberF f F σ) :=
  eqToIso
    (congrArg (fun k ↦ (Modules.pullback k).obj F)
      ((pullback.lift_fst (pullback.fst f τ.hom ≫ 𝟙 X)
          (pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left)
          (((Category.assoc (pullback.fst f τ.hom) (𝟙 X) f).trans
              (congrArg (fun k ↦ pullback.fst f τ.hom ≫ k) (Category.id_comp f))).trans
            ((pullback.condition).trans
              ((congrArg (fun k ↦ pullback.snd f τ.hom ≫ k)
                  (CostructuredArrow.w h).symm).trans
                (Category.assoc (pullback.snd f τ.hom)
                  ((ofOverFunctor S).map h.left) σ.hom).symm)))).trans
        (Category.comp_id _)).symm) ≪≫
    (Modules.pullbackCompIso (fiberMap f h) (pullback.fst f σ.hom)).symm.app F

/-- Unfolding of `fiberFCompIso`. -/
theorem fiberFCompIso_eq (f : X ⟶ B) (F : X.Modules) {σ τ : SchemeOver B}
    (h : τ ⟶ σ) :
    fiberFCompIso f F h =
      eqToIso
          (congrArg (fun k ↦ (Modules.pullback k).obj F)
            ((pullback.lift_fst (pullback.fst f τ.hom ≫ 𝟙 X)
                (pullback.snd f τ.hom ≫ (ofOverFunctor S).map h.left)
                (((Category.assoc (pullback.fst f τ.hom) (𝟙 X) f).trans
                    (congrArg (fun k ↦ pullback.fst f τ.hom ≫ k)
                      (Category.id_comp f))).trans
                  ((pullback.condition).trans
                    ((congrArg (fun k ↦ pullback.snd f τ.hom ≫ k)
                        (CostructuredArrow.w h).symm).trans
                      (Category.assoc (pullback.snd f τ.hom)
                        ((ofOverFunctor S).map h.left) σ.hom).symm)))).trans
              (Category.comp_id _)).symm) ≪≫
        (Modules.pullbackCompIso (fiberMap f h) (pullback.fst f σ.hom)).symm.app F :=
  sorry

/-- A finitely presented quasi-coherent quotient of `F_T` that is flat over `T`
and has support proper over `T`. -/
structure QuotPoint (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B)
    [FinitePresentation f] where
  /-- The target module sheaf of the quotient. -/
  module : (fiber f σ).Modules
  /-- The quotient morphism from `F_T`. -/
  map : fiberF f F σ ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The target is of finite presentation. -/
  isFinitePresentation : module.IsFinitePresentation
  /-- The target is flat over the test scheme. -/
  isFlat : flatOver module (fiberToBase f σ)
  /-- The support of the target is proper over the test scheme. -/
  hasProperSupport : Modules.HasProperSupportOver (fiberToBase f σ) module

namespace QuotPoint

/-- Package an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent of finite presentation,
flat over `T`, and with support proper over `T`, as a Quot-point. -/
def ofEpi (f : X ⟶ B) (F : X.Modules) (σ : SchemeOver B) [FinitePresentation f]
    (module : (fiber f σ).Modules) (map : fiberF f F σ ⟶ module) (map_epi : Epi map)
    (isQuasicoherent : module.IsQuasicoherent)
    (isFinitePresentation : module.IsFinitePresentation)
    (isFlat : flatOver module (fiberToBase f σ))
    (hasProperSupport : Modules.HasProperSupportOver (fiberToBase f σ) module) :
    QuotPoint f F σ where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent
  isFinitePresentation := isFinitePresentation
  isFlat := isFlat
  hasProperSupport := hasProperSupport

/-- A Quot-point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent of finite
presentation, flat over `T`, and with support proper over `T`. -/
theorem spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} [FinitePresentation f]
    (Q : QuotPoint f F σ) :
    Epi Q.map ∧ Q.module.IsQuasicoherent ∧ Q.module.IsFinitePresentation ∧
      flatOver Q.module (fiberToBase f σ) ∧
      Modules.HasProperSupportOver (fiberToBase f σ) Q.module :=
  sorry

/-- Pull back a Quot-point along a morphism of schemes over `B`. -/
def pullback {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B} [FinitePresentation f]
    (Q : QuotPoint f F σ) (h : τ ⟶ σ) : QuotPoint f F τ where
  module := (Modules.pullback (fiberMap f h)).obj Q.module
  map := (fiberFCompIso f F h).hom ≫ (Modules.pullback (fiberMap f h)).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry
  isFinitePresentation := sorry
  isFlat := sorry
  hasProperSupport := sorry

/-- The module of a pulled-back Quot-point is the module pullback along `fiberMap`. -/
theorem pullback_module {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).module = (Modules.pullback (fiberMap f h)).obj Q.module :=
  sorry

/-- Two Quot-points are identified when there is an isomorphism of targets over `F_T`. -/
def Rel {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B} [FinitePresentation f]
    (Q₁ Q₂ : QuotPoint f F σ) : Prop :=
  ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map

/-- Kernel identification of Quot-points is equivalent to an isomorphism of targets over `F_T`. -/
theorem rel_iso_iff {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map :=
  sorry

end QuotPoint

/-- Kernel identification is an equivalence relation on Quot-points. -/
theorem quotSetoid_isEquivalence (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    (σ : SchemeOver B) :
    Equivalence (@QuotPoint.Rel _ _ _ f F σ _) :=
  sorry

/-- The setoid of Quot-points modulo kernel identification. -/
def quotSetoid (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) (σ : SchemeOver B) :
    Setoid (QuotPoint f F σ) where
  r := QuotPoint.Rel
  iseqv := quotSetoid_isEquivalence f F σ

/-- Pullback preserves kernel identification of Quot-points. -/
theorem quotSetoid_rel_pullback (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    ∀ Q₁ Q₂ : QuotPoint f F σ,
      (quotSetoid f F σ).r Q₁ Q₂ →
        (quotSetoid f F τ).r (Q₁.pullback h) (Q₂.pullback h) :=
  sorry

/-- The Grothendieck Quot functor `Quot_{F/X/B}` of finitely presented
quasi-coherent quotients of `F` along a finite-presentation morphism
`f : X ⟶ B`, identified by kernels, flat over the test scheme, and with
support proper over the test scheme. -/
def quot (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] :
    (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := _root_.Quotient (quotSetoid f F σ.unop)
  map {σ τ} (h : σ ⟶ τ) :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.pullback h.unop)
        (quotSetoid_rel_pullback f F h.unop))
  map_id := sorry
  map_comp := sorry

/-- Evaluating the Quot functor at a scheme over `B` yields kernel-identified Quot-points. -/
theorem quot_obj (f : X ⟶ B) [FinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] (σ : SchemeOver B) :
    (quot f F).obj (op σ) = _root_.Quotient (quotSetoid f F σ) :=
  sorry

end AlgebraicGeometry.NonseparatedAlgebraization
