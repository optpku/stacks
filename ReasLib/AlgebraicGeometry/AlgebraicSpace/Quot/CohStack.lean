/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import Mathlib.CategoryTheory.Elements

/-! # The forgetful functor from quotients to coherent sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

-- Local declaration justification (metaprogramming implementation): Exposed categorical data uses private concrete maps and named proof laws, which Lean's module visibility requires exporting internally.
set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace QuotPoint

/-- A quotient determines its finitely presented flat target with proper support,
over the same test scheme. -/
def toCohStack {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : CohStack.Obj f where
  σ := σ
  module := Q.point.module
  isFinitePresentation := Q.isFinitePresentation
  isFlat := Q.point.isFlat
  hasProperSupport := ⟨Q.hasProperSupport⟩

/-- Forgetting a quotient retains its base and target, finite presentation,
flatness and proper support. -/
theorem toCohStack_spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.toCohStack.σ = σ ∧ Q.toCohStack.module = Q.point.module ∧
      Q.toCohStack.module.IsFinitePresentation ∧
      Modules.flatOver Q.toCohStack.module (CohStack.fiberToBase f σ) ∧
      Modules.HasProperSupportOver (CohStack.fiberToBase f σ) Q.toCohStack.module := sorry

/-- Equal quotient kernels force the second quotient map to annihilate the first kernel. -/
private theorem kernel_comp_zero_of_rel {f : X ⟶ B} {F : X.Modules}
    {σ : SchemeOver B} [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ)
    (h : Rel Q₁.point Q₂.point) :
    kernel.ι Q₁.point.map ≫ Q₂.point.map = 0 := sorry

/-- Descent of a quotient epimorphism through another quotient with the same kernel. -/
private def relMap {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point) :
    Q₁.point.module ⟶ Q₂.point.module :=
  @Abelian.epiDesc _ _ _ _ _ Q₁.point.map Q₁.point.map_epi _
    Q₂.point.map (kernel_comp_zero_of_rel Q₁ Q₂ h)

/-- The two descent maps between quotients with equal kernels are inverse. -/
private theorem relMap_inv {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point) :
    relMap Q₁ Q₂ h ≫ relMap Q₂ Q₁ (Eq.symm h) = 𝟙 Q₁.point.module := sorry

/-- Quotients with equal kernels have canonically isomorphic targets by epimorphism descent. -/
def relIso {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point) :
    Q₁.point.module ≅ Q₂.point.module where
  hom := relMap Q₁ Q₂ h
  inv := relMap Q₂ Q₁ (Eq.symm h)
  hom_inv_id := relMap_inv Q₁ Q₂ h
  inv_hom_id := relMap_inv Q₂ Q₁ (Eq.symm h)

/-- The canonical target isomorphism is the unique isomorphism commuting with the quotient maps. -/
theorem relIso_spec {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point) :
    Q₁.point.map ≫ (relIso Q₁ Q₂ h).hom = Q₂.point.map ∧
      ∀ e : Q₁.point.module ≅ Q₂.point.module,
        Q₁.point.map ≫ e.hom = Q₂.point.map → e = relIso Q₁ Q₂ h := sorry

/-- Equal-kernel quotients induce a coherent-object morphism over the identity base map. -/
def relCohHom {f : X ⟶ B} {F : X.Modules} {σ : SchemeOver B}
    [FinitePresentation f] (Q₁ Q₂ : QuotPoint f F σ) (h : Rel Q₁.point Q₂.point) :
    Q₁.toCohStack ⟶ Q₂.toCohStack :=
  CohStack.homMk (𝟙 σ) (CohStack.Hom.idIso Q₂.toCohStack ≪≫ (relIso Q₁ Q₂ h).symm)

/-- Pullback of a quotient induces a coherent-object morphism over the supplied base map. -/
def pullbackCohHom {f : X ⟶ B} {F : X.Modules} {σ τ : SchemeOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) (h : τ ⟶ σ) :
    (Q.pullback h).toCohStack ⟶ Q.toCohStack :=
  CohStack.homMk h (Iso.refl _)

end QuotPoint

/-- An arrow between quotient classes identifies the source representative with
the pullback of the target representative by equality of kernels. -/
private theorem representative_pullback_rel (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] {a b : (quot f F).Elementsᵒᵖ} (α : a ⟶ b) :
    Rel (_root_.Quotient.out a.unop.snd).point
      ((_root_.Quotient.out b.unop.snd).pullback α.unop.val.unop).point := sorry

/-- The coherent-object arrow induced by a map of quotient classes. -/
private def forgetCohMap (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] {a b : (quot f F).Elementsᵒᵖ} (α : a ⟶ b) :
    (_root_.Quotient.out a.unop.snd).toCohStack ⟶
      (_root_.Quotient.out b.unop.snd).toCohStack :=
  QuotPoint.relCohHom (_root_.Quotient.out a.unop.snd)
      ((_root_.Quotient.out b.unop.snd).pullback α.unop.val.unop)
      (representative_pullback_rel f F α) ≫
    QuotPoint.pullbackCohHom (_root_.Quotient.out b.unop.snd) α.unop.val.unop

/-- The coherent-object arrow assigned to an identity is the identity. -/
private theorem forgetCoh_map_id (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (a : (quot f F).Elementsᵒᵖ) :
    forgetCohMap f F (𝟙 a) = 𝟙 (_root_.Quotient.out a.unop.snd).toCohStack := sorry

/-- The coherent-object arrow assignment preserves composition. -/
private theorem forgetCoh_map_comp (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] {a b c : (quot f F).Elementsᵒᵖ}
    (α : a ⟶ b) (β : b ⟶ c) :
    forgetCohMap f F (α ≫ β) = forgetCohMap f F α ≫ forgetCohMap f F β := sorry

/-- The forgetful functor sends a quotient class to its coherent target and
base change to the canonical pullback isomorphism of targets. -/
def forgetCoh (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] :
    (quot f F).Elementsᵒᵖ ⥤ CohStack.Obj f where
  obj a := (_root_.Quotient.out a.unop.snd).toCohStack
  map α := forgetCohMap f F α
  map_id := forgetCoh_map_id f F
  map_comp := forgetCoh_map_comp f F

/-- Forgetting a quotient commutes with projection to schemes over the ambient scheme. -/
theorem forgetCoh_over (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] :
    forgetCoh f F ⋙ CohStack.p f =
      (CategoryOfElements.π (quot f F)).leftOp ⋙
        CostructuredArrow.proj (ofOverFunctor S) B := sorry

/-- For every representative, the forgotten module is uniquely isomorphic to
its target compatibly with the quotient epimorphism, over the original test scheme. -/
theorem forgetCoh_spec (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (σ : SchemeOver B) (q : (quot f F).obj (op σ))
    (Q : QuotPoint f F σ) (hQ : _root_.Quotient.mk (quotSetoid f F σ) Q = q) :
    ((forgetCoh f F).obj (op ((quot f F).elementsMk (op σ) q))).σ = σ ∧
      ∃! e : ((forgetCoh f F).obj (op ((quot f F).elementsMk (op σ) q))).module ≅
          Q.point.module,
        (_root_.Quotient.out q).point.map ≫ e.hom = Q.point.map := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
