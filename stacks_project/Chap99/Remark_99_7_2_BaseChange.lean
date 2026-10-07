module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap99.«99_7_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

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

/-- Viewing a scheme `T` over `B'` as a scheme over `B` via `T ⟶ B' ⟶ B` composes
the structure morphism with `g`. -/
theorem changeBase_hom (g : B' ⟶ B) (σ : SchemesOver B') :
    ((CostructuredArrow.map g).obj σ).hom = σ.hom ≫ g :=
  rfl

/-- The canonical identification `(X ×_B B') ×_{B'} T ≅ X ×_B T`. -/
def fiberIso (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    fiber (pullback.snd f g) σ ≅ fiber f ((CostructuredArrow.map g).obj σ) :=
  pullbackLeftPullbackSndIso f g σ.hom

/-- The first projection of `fiberIso.hom` is the composite of the projections to `X`. -/
theorem fiberIso_fst (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.fst f ((CostructuredArrow.map g).obj σ).hom =
      pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g :=
  sorry

/-- The second projection of `fiberIso.hom` recovers the projection to `T`. -/
theorem fiberIso_snd (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.snd f ((CostructuredArrow.map g).obj σ).hom =
      pullback.snd (pullback.snd f g) σ.hom :=
  sorry

/-- The comparison identifying `F'_T` with the pullback of `F_T` along `fiberIso.hom`. -/
def fiberFIso (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    fiberF (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ ≅
      (Modules.pullback (fiberIso f g σ).hom).obj
        (fiberF f F ((CostructuredArrow.map g).obj σ)) :=
  (Modules.pullbackComp (pullback.fst (pullback.snd f g) σ.hom) (pullback.fst f g)).app F ≪≫
    eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      (pullbackLeftPullbackSndIso_hom_fst f g σ.hom).symm) ≪≫
    (Modules.pullbackComp (fiberIso f g σ).hom
      (pullback.fst f ((CostructuredArrow.map g).obj σ).hom)).symm.app F

/-- The forward component of `fiberFIso` is the indicated composite of module pullbacks. -/
theorem fiberFIso_hom (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    (fiberFIso f g F σ).hom =
      ((Modules.pullbackComp (pullback.fst (pullback.snd f g) σ.hom)
          (pullback.fst f g)).app F).hom ≫
        (eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
            (pullbackLeftPullbackSndIso_hom_fst f g σ.hom).symm)).hom ≫
          ((Modules.pullbackComp (fiberIso f g σ).hom
              (pullback.fst f ((CostructuredArrow.map g).obj σ).hom)).symm.app F).hom :=
  sorry

/-- The comparison identifying `F_T` with the pullback of `F'_T` along `fiberIso.inv`. -/
def fiberFIsoInv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    fiberF f F ((CostructuredArrow.map g).obj σ) ≅
      (Modules.pullback (fiberIso f g σ).inv).obj
        (fiberF (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :=
  eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      (pullbackLeftPullbackSndIso_inv_fst f g σ.hom).symm) ≪≫
    (Modules.pullbackComp (fiberIso f g σ).inv
      (pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g)).symm.app F ≪≫
    (Modules.pullback (fiberIso f g σ).inv).mapIso
      ((Modules.pullbackComp (pullback.fst (pullback.snd f g) σ.hom)
          (pullback.fst f g)).symm.app F)

/-- The forward component of `fiberFIsoInv` is the indicated composite of module pullbacks. -/
theorem fiberFIsoInv_hom (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    (fiberFIsoInv f g F σ).hom =
      (eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
          (pullbackLeftPullbackSndIso_inv_fst f g σ.hom).symm)).hom ≫
        ((Modules.pullbackComp (fiberIso f g σ).inv
            (pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g)).symm.app F).hom ≫
          ((Modules.pullback (fiberIso f g σ).inv).mapIso
            ((Modules.pullbackComp (pullback.fst (pullback.snd f g) σ.hom)
                (pullback.fst f g)).symm.app F)).hom :=
  sorry

/-- Transport a quotient point on `X'_T` to a quotient point on `X_T` along `fiberIso`. -/
def pointMap {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemesOver B'}
    (Q : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    Point f F ((CostructuredArrow.map g).obj σ) where
  module := (Modules.pullback (fiberIso f g σ).inv).obj Q.module
  map := (fiberFIsoInv f g F σ).hom ≫ (Modules.pullback (fiberIso f g σ).inv).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry
  isFlat := sorry

/-- Transport a quotient point on `X_T` to a quotient point on `X'_T` along `fiberIso`. -/
def pointInv {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemesOver B'}
    (Q : Point f F ((CostructuredArrow.map g).obj σ)) :
    Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ where
  module := (Modules.pullback (fiberIso f g σ).hom).obj Q.module
  map := (fiberFIso f g F σ).hom ≫ (Modules.pullback (fiberIso f g σ).hom).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry
  isFlat := sorry

/-- The module of `pointMap Q` is the module pullback along `fiberIso.inv`. -/
theorem pointMap_module {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemesOver B'}
    (Q : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    (pointMap Q).module = (Modules.pullback (fiberIso f g σ).inv).obj Q.module :=
  sorry

/-- Transport of quotient points along `fiberIso` preserves kernel identification. -/
theorem pointMap_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    ∀ (Q₁ Q₂ : Point (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ),
      Rel Q₁ Q₂ → Rel (pointMap Q₁) (pointMap Q₂) :=
  sorry

/-- The inverse transport of quotient points along `fiberIso` preserves kernel identification. -/
theorem pointInv_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    ∀ (Q₁ Q₂ : Point f F ((CostructuredArrow.map g).obj σ)),
      Rel Q₁ Q₂ → Rel (pointInv Q₁) (pointInv Q₂) :=
  sorry

/-- Transport a finitely presented quotient point on `X'_T` to `X_T` along `fiberIso`. -/
def fpPointMap {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemesOver B'}
    (Q : FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ) :
    FpPoint f F ((CostructuredArrow.map g).obj σ) where
  point := pointMap Q.point
  isFinitePresentation := sorry

/-- Transport a finitely presented quotient point on `X_T` to `X'_T` along `fiberIso`. -/
def fpPointInv {f : X ⟶ B} {g : B' ⟶ B} {F : X.Modules} {σ : SchemesOver B'}
    (Q : FpPoint f F ((CostructuredArrow.map g).obj σ)) :
    FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ where
  point := pointInv Q.point
  isFinitePresentation := sorry

/-- Transport of finitely presented quotient points along `fiberIso` preserves kernel
identification. -/
theorem fpPointMap_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    ∀ (Q₁ Q₂ : FpPoint (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) σ),
      Rel Q₁.point Q₂.point → Rel (fpPointMap Q₁).point (fpPointMap Q₂).point :=
  sorry

/-- The inverse transport of finitely presented quotient points preserves kernel
identification. -/
theorem fpPointInv_rel (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) (σ : SchemesOver B') :
    ∀ (Q₁ Q₂ : FpPoint f F ((CostructuredArrow.map g).obj σ)),
      Rel Q₁.point Q₂.point → Rel (fpPointInv Q₁).point (fpPointInv Q₂).point :=
  sorry

/-- The objectwise equivalence identifying `Q_{F'/X'/B'}` with `Q_{F/X/B}` after
changing the base along `g`. -/
def functorChangeBaseEquiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemesOver B')ᵒᵖ) :
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
    [F.IsQuasicoherent] (σ : (SchemesOver B')ᵒᵖ) :
    (functorChangeBaseIso f g F).app σ = (functorChangeBaseEquiv f g F σ).toIso :=
  sorry

/-- The objectwise equivalence identifying `Q^{fp}_{F'/X'/B'}` with `Q^{fp}_{F/X/B}` after
changing the base along `g`. -/
def fpFunctorChangeBaseEquiv (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemesOver B')ᵒᵖ) :
    (fpFunctor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F)).obj σ ≃
      ((CostructuredArrow.map g).op ⋙ fpFunctor f F).obj σ where
  toFun :=
    _root_.Quotient.map (fun Q ↦ fpPointMap Q) (fpPointMap_rel f g F σ.unop)
  invFun :=
    _root_.Quotient.map (fun Q ↦ fpPointInv Q) (fpPointInv_rel f g F σ.unop)
  left_inv := sorry
  right_inv := sorry

/-- The natural isomorphism
`Q^{fp}_{F'/X'/B'} ≅ (CostructuredArrow.map g).op ⋙ Q^{fp}_{F/X/B}`. -/
def fpFunctorChangeBaseIso (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    fpFunctor (pullback.snd f g) ((Modules.pullback (pullback.fst f g)).obj F) ≅
      (CostructuredArrow.map g).op ⋙ fpFunctor f F :=
  NatIso.ofComponents (fun σ ↦ (fpFunctorChangeBaseEquiv f g F σ).toIso) sorry

/-- The component of `fpFunctorChangeBaseIso` is the objectwise finitely presented
base-change equivalence. -/
theorem fpFunctorChangeBaseIso_app (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent] (σ : (SchemesOver B')ᵒᵖ) :
    (fpFunctorChangeBaseIso f g F).app σ = (fpFunctorChangeBaseEquiv f g F σ).toIso :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
