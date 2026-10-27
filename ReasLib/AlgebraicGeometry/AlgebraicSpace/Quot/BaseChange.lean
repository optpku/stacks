/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation

/-!
# Base change of the functors of quotients

For a morphism `g : B' ⟶ B` of algebraic spaces, the fibre product `X' = X ×_B B'`
and the pullback module `F'` of a quasi-coherent module `F` on `X` yield canonical
identifications of `Q_{F'/X'/B'}` and `Q^{fp}_{F'/X'/B'}` with the original functors
after viewing a test scheme over `B'` as a scheme over `B` via `CostructuredArrow.map g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- The canonical identification `(X ×_B B') ×_{B'} T ≅ X ×_B T`. -/
def fiberIso (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemeOver B') :
    fiber (pullback.snd f g) σ ≅ fiber f ((CostructuredArrow.map g).obj σ) :=
  pullbackLeftPullbackSndIso f g σ.hom

/-- The comparison identifying `F'_T` with the pullback of `F_T` along `fiberIso.hom`. -/
def fiberFIso (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    fiberF (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ ≅
      (Modules.pullback (fiberIso f g σ).hom).obj
        (fiberF f F ((CostructuredArrow.map g).obj σ)) :=
  (Modules.pullbackCompIso (pullback.fst (pullback.snd f g) σ.hom) (pullback.fst f g)).app F ≪≫
    eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      (pullbackLeftPullbackSndIso_hom_fst f g σ.hom).symm) ≪≫
    (Modules.pullbackCompIso (fiberIso f g σ).hom
      (pullback.fst f ((CostructuredArrow.map g).obj σ).hom)).symm.app F

/-- The forward component of `fiberFIso` is the indicated composite of module pullbacks. -/
theorem fiberFIso_hom (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    (fiberFIso f g F σ).hom =
      ((Modules.pullbackCompIso (pullback.fst (pullback.snd f g) σ.hom)
          (pullback.fst f g)).app F).hom ≫
        (eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
            (pullbackLeftPullbackSndIso_hom_fst f g σ.hom).symm)).hom ≫
          ((Modules.pullbackCompIso (fiberIso f g σ).hom
              (pullback.fst f ((CostructuredArrow.map g).obj σ).hom)).symm.app F).hom :=
  by
    simp only [fiberFIso, Iso.trans_hom]
    congr 2

/-- The comparison identifying `F_T` with the pullback of `F'_T` along `fiberIso.inv`. -/
def fiberFIsoInv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    fiberF f F ((CostructuredArrow.map g).obj σ) ≅
      (Modules.pullback (fiberIso f g σ).inv).obj
        (fiberF (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :=
  eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      (pullbackLeftPullbackSndIso_inv_fst f g σ.hom).symm) ≪≫
    (Modules.pullbackCompIso (fiberIso f g σ).inv
      (pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g)).symm.app F ≪≫
    (Modules.pullback (fiberIso f g σ).inv).mapIso
      ((Modules.pullbackCompIso (pullback.fst (pullback.snd f g) σ.hom)
          (pullback.fst f g)).symm.app F)

/-- The forward component of `fiberFIsoInv` is the indicated composite of module pullbacks. -/
theorem fiberFIsoInv_hom (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    (fiberFIsoInv f g F σ).hom =
      (eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
          (pullbackLeftPullbackSndIso_inv_fst f g σ.hom).symm)).hom ≫
        ((Modules.pullbackCompIso (fiberIso f g σ).inv
            (pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g)).symm.app F).hom ≫
          ((Modules.pullback (fiberIso f g σ).inv).mapIso
            ((Modules.pullbackCompIso (pullback.fst (pullback.snd f g) σ.hom)
                (pullback.fst f g)).symm.app F)).hom :=
  by
    simp only [fiberFIsoInv, Iso.trans_hom]
    congr 1

/-- Transport a quotient point on `X'_T` to a quotient point on `X_T` along `fiberIso`. -/
def pointMap {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemeOver B'}
    (Q : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    Point f F ((CostructuredArrow.map g).obj σ) where
  module := (Modules.pullback (fiberIso f g σ).inv).obj Q.module
  map := (fiberFIsoInv f g F σ).hom ≫ (Modules.pullback (fiberIso f g σ).inv).map Q.map
  map_epi := by
    letI := Q.map_epi
    infer_instance
  isQuasicoherent :=
    Modules.pullback_quasiCoherentModuleProperty (fiberIso f g σ).inv Q.isQuasicoherent
  isFlat := by
    letI := Q.isQuasicoherent
    refine Modules.flatOver_pullback_of_isPullback (fiberIso f g σ).inv
      (pullback.snd f ((CostructuredArrow.map g).obj σ).hom)
      (pullback.snd (pullback.snd f g) σ.hom) (𝟙 _) ?_ Q.module Q.isFlat
    exact IsPullback.of_horiz_isIso (g := 𝟙 (ofOver σ.left))
      ⟨by
        change (pullbackLeftPullbackSndIso f g σ.hom).inv ≫
            pullback.snd (pullback.snd f g) σ.hom =
          pullback.snd f (σ.hom ≫ g) ≫ 𝟙 _
        rw [Category.comp_id]
        exact pullbackLeftPullbackSndIso_inv_snd_snd (C := AlgebraicSpace S) f g σ.hom⟩

/-- Transport a quotient point on `X_T` to a quotient point on `X'_T` along `fiberIso`. -/
def pointInv {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemeOver B'}
    (Q : Point f F ((CostructuredArrow.map g).obj σ)) :
    Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ where
  module := (Modules.pullback (fiberIso f g σ).hom).obj Q.module
  map := (fiberFIso f g F σ).hom ≫ (Modules.pullback (fiberIso f g σ).hom).map Q.map
  map_epi := by
    letI := Q.map_epi
    infer_instance
  isQuasicoherent :=
    Modules.pullback_quasiCoherentModuleProperty (fiberIso f g σ).hom Q.isQuasicoherent
  isFlat := by
    letI := Q.isQuasicoherent
    refine Modules.flatOver_pullback_of_isPullback (fiberIso f g σ).hom
      (pullback.snd (pullback.snd f g) σ.hom)
      (pullback.snd f ((CostructuredArrow.map g).obj σ).hom) (𝟙 _) ?_ Q.module Q.isFlat
    exact IsPullback.of_horiz_isIso (g := 𝟙 (ofOver σ.left))
      ⟨by
        change (pullbackLeftPullbackSndIso f g σ.hom).hom ≫
            pullback.snd f (σ.hom ≫ g) =
          pullback.snd (pullback.snd f g) σ.hom ≫ 𝟙 _
        rw [Category.comp_id]
        exact pullbackLeftPullbackSndIso_hom_snd (C := AlgebraicSpace S) f g σ.hom⟩

/-- The module of `pointMap Q` is the module pullback along `fiberIso.inv`. -/
theorem pointMap_module {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemeOver B'}
    (Q : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    (pointMap Q).module = (Modules.pullback (fiberIso f g σ).inv).obj Q.module :=
  rfl

-- Equal kernels of epimorphisms give factorizations in both directions. Applying
-- any functor and precomposing with a fixed map preserves these factorizations.
private theorem kernelSubobject_map_precomp_eq
    {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasZeroMorphisms D] [HasKernels D] (H : C ⥤ D)
    {M Q₁ Q₂ : C} {P : D} (e : P ⟶ H.obj M)
    (p₁ : M ⟶ Q₁) (p₂ : M ⟶ Q₂) [Epi p₁] [Epi p₂]
    (h : kernelSubobject p₁ = kernelSubobject p₂) :
    kernelSubobject (e ≫ H.map p₁) = kernelSubobject (e ≫ H.map p₂) := by
  have factor {Y Z : C} (p : M ⟶ Y) [Epi p] (q : M ⟶ Z)
      (hpq : kernelSubobject p = kernelSubobject q) :
      ∃ a : Y ⟶ Z, p ≫ a = q := by
    have hk : (kernelSubobject p).arrow ≫ q = 0 := by
      rw [hpq]
      exact kernelSubobject_arrow_comp q
    have hk' : kernel.ι p ≫ q = 0 := by
      rw [← kernelSubobject_arrow' p, Category.assoc, hk, comp_zero]
    exact ⟨Abelian.epiDesc p q hk', Abelian.comp_epiDesc p q hk'⟩
  obtain ⟨a, ha⟩ := factor p₁ p₂ h
  obtain ⟨b, hb⟩ := factor p₂ p₁ h.symm
  have ha' : (e ≫ H.map p₁) ≫ H.map a = e ≫ H.map p₂ := by
    rw [Category.assoc, ← H.map_comp, ha]
  have hb' : (e ≫ H.map p₂) ≫ H.map b = e ≫ H.map p₁ := by
    rw [Category.assoc, ← H.map_comp, hb]
  apply le_antisymm
  · apply le_kernelSubobject
    rw [← ha', ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
  · apply le_kernelSubobject
    rw [← hb', ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]

/-- Transport of quotient points along `fiberIso` preserves kernel identification. -/
theorem pointMap_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    ∀ (Q₁ Q₂ : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ),
      Rel Q₁ Q₂ → Rel (pointMap Q₁) (pointMap Q₂) :=
  by
    intro Q₁ Q₂ h
    letI := Q₁.map_epi
    letI := Q₂.map_epi
    exact kernelSubobject_map_precomp_eq (Modules.pullback (fiberIso f g σ).inv)
      (fiberFIsoInv f g F σ).hom Q₁.map Q₂.map h

/-- The inverse transport of quotient points along `fiberIso` preserves kernel identification. -/
theorem pointInv_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    ∀ (Q₁ Q₂ : Point f F ((CostructuredArrow.map g).obj σ)),
      Rel Q₁ Q₂ → Rel (pointInv Q₁) (pointInv Q₂) :=
  by
    intro Q₁ Q₂ h
    letI := Q₁.map_epi
    letI := Q₂.map_epi
    exact kernelSubobject_map_precomp_eq (Modules.pullback (fiberIso f g σ).hom)
      (fiberFIso f g F σ).hom Q₁.map Q₂.map h

/-- Transport a finitely presented quotient point on `X'_T` to `X_T` along `fiberIso`. -/
def fpPointMap {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemeOver B'}
    (Q : FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    FpPoint f F ((CostructuredArrow.map g).obj σ) where
  point := pointMap Q.point
  isFinitePresentation := sorry

/-- Transport a finitely presented quotient point on `X_T` to `X'_T` along `fiberIso`. -/
def fpPointInv {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemeOver B'}
    (Q : FpPoint f F ((CostructuredArrow.map g).obj σ)) :
    FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ where
  point := pointInv Q.point
  isFinitePresentation := sorry

/-- Transport of finitely presented quotient points along `fiberIso` preserves kernel
identification. -/
theorem fpPointMap_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    ∀ (Q₁ Q₂ : FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ),
      Rel Q₁.point Q₂.point → Rel (fpPointMap Q₁).point (fpPointMap Q₂).point :=
  fun Q₁ Q₂ h ↦ pointMap_rel f g F σ Q₁.point Q₂.point h

/-- The inverse transport of finitely presented quotient points preserves kernel
identification. -/
theorem fpPointInv_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemeOver B') :
    ∀ (Q₁ Q₂ : FpPoint f F ((CostructuredArrow.map g).obj σ)),
      Rel Q₁.point Q₂.point → Rel (fpPointInv Q₁).point (fpPointInv Q₂).point :=
  fun Q₁ Q₂ h ↦ pointInv_rel f g F σ Q₁.point Q₂.point h

/-- The objectwise equivalence identifying `Q_{F'/X'/B'}` with `Q_{F/X/B}` after
changing the base along `g`. -/
def functorChangeBaseEquiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B')ᵒᵖ) :
    (functor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F)).obj σ ≃
      ((CostructuredArrow.map g).op ⋙ functor f F).obj σ where
  toFun :=
    _root_.Quotient.map (fun Q ↦ pointMap Q) (pointMap_rel f g F σ.unop)
  invFun :=
    _root_.Quotient.map (fun Q ↦ pointInv Q) (pointInv_rel f g F σ.unop)
  left_inv := sorry
  right_inv := sorry

/-- The natural isomorphism `Q_{F'/X'/B'} ≅ (CostructuredArrow.map g).op ⋙ Q_{F/X/B}`. -/
def functorChangeBaseIso (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    functor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) ≅
      (CostructuredArrow.map g).op ⋙ functor f F :=
  NatIso.ofComponents (fun σ ↦ (functorChangeBaseEquiv f g F σ).toIso) sorry

/-- The component of `functorChangeBaseIso` is the objectwise base-change equivalence. -/
theorem functorChangeBaseIso_app (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemeOver B')ᵒᵖ) :
    (functorChangeBaseIso f g F).app σ = (functorChangeBaseEquiv f g F σ).toIso :=
  rfl

/-- The objectwise equivalence identifying `Q^{fp}_{F'/X'/B'}` with `Q^{fp}_{F/X/B}` after
changing the base along `g`. -/
def fpFunctorChangeBaseEquiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B')ᵒᵖ) :
    (fpFunctor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F)).obj σ ≃
      ((CostructuredArrow.map g).op ⋙ fpFunctor f F).obj σ where
  toFun :=
    _root_.Quotient.map (fun Q ↦ fpPointMap Q) (fpPointMap_rel f g F σ.unop)
  invFun :=
    _root_.Quotient.map (fun Q ↦ fpPointInv Q) (fpPointInv_rel f g F σ.unop)
  left_inv := by
    intro q
    refine _root_.Quotient.inductionOn q ?_
    intro Q
    apply _root_.Quotient.sound
    change Rel (pointInv (pointMap Q.point)) Q.point
    exact _root_.Quotient.exact
      ((functorChangeBaseEquiv f g F σ).left_inv (_root_.Quotient.mk _ Q.point))
  right_inv := by
    intro q
    refine _root_.Quotient.inductionOn q ?_
    intro Q
    apply _root_.Quotient.sound
    change Rel (pointMap (pointInv Q.point)) Q.point
    exact _root_.Quotient.exact
      ((functorChangeBaseEquiv f g F σ).right_inv (_root_.Quotient.mk _ Q.point))

/-- The natural isomorphism
`Q^{fp}_{F'/X'/B'} ≅ (CostructuredArrow.map g).op ⋙ Q^{fp}_{F/X/B}`. -/
def fpFunctorChangeBaseIso (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    fpFunctor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) ≅
      (CostructuredArrow.map g).op ⋙ fpFunctor f F :=
  NatIso.ofComponents (fun σ ↦ (fpFunctorChangeBaseEquiv f g F σ).toIso) (by
    intro σ τ h
    apply ConcreteCategory.hom_ext
    intro q
    refine _root_.Quotient.inductionOn q ?_
    intro Q
    change _root_.Quotient.mk _ (fpPointMap (Q.pullback h.unop)) =
      _root_.Quotient.mk _ ((fpPointMap Q).pullback ((CostructuredArrow.map g).map h.unop))
    apply _root_.Quotient.sound
    change Rel (pointMap (Q.point.pullback h.unop))
      ((pointMap Q.point).pullback ((CostructuredArrow.map g).map h.unop))
    exact _root_.Quotient.exact
      (ConcreteCategory.congr_hom ((functorChangeBaseIso f g F).hom.naturality h)
        (_root_.Quotient.mk _ Q.point)))

/-- The component of `fpFunctorChangeBaseIso` is the objectwise finitely presented
base-change equivalence. -/
theorem fpFunctorChangeBaseIso_app (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemeOver B')ᵒᵖ) :
    (fpFunctorChangeBaseIso f g F).app σ = (fpFunctorChangeBaseEquiv f g F σ).toIso :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Quot
