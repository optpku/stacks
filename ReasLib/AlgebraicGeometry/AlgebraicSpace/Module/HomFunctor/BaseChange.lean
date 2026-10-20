module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor

/-!
# Base change of the Hom functor of quasi-coherent modules
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Pullback of `F'_T` along the inverse pasting isomorphism is identified with
`F_T`. -/
def homFunctorBaseChangeModuleIso (f : X ⟶ B) (φ : B' ⟶ B) (F : X.Modules)
    (σ : SchemeOver B') :
    (pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).obj
        (baseChangeModule (pullback.snd f φ) σ.hom
          ((pullback (pullback.fst f φ)).obj F)) ≅
      baseChangeModule f ((CostructuredArrow.map φ).obj σ).hom F :=
  (pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).mapIso
      ((pullbackCompIso (pullback.fst (pullback.snd f φ) σ.hom) (pullback.fst f φ)).app F) ≪≫
    (pullbackCompIso (pullbackLeftPullbackSndIso f φ σ.hom).inv
        (pullback.fst (pullback.snd f φ) σ.hom ≫ pullback.fst f φ)).app F ≪≫
    (pullbackCongr (pullbackLeftPullbackSndIso_inv_fst f φ σ.hom)).app F

/-- Pullback of `F_T` along the pasting isomorphism is identified with `F'_T`. -/
def homFunctorBaseChangeModuleIsoInv (f : X ⟶ B) (φ : B' ⟶ B) (F : X.Modules)
    (σ : SchemeOver B') :
    (pullback (pullbackLeftPullbackSndIso f φ σ.hom).hom).obj
        (baseChangeModule f ((CostructuredArrow.map φ).obj σ).hom F) ≅
      baseChangeModule (pullback.snd f φ) σ.hom
        ((pullback (pullback.fst f φ)).obj F) :=
  (pullbackCompIso (pullbackLeftPullbackSndIso f φ σ.hom).hom
        (pullback.fst f ((CostructuredArrow.map φ).obj σ).hom)).app F ≪≫
    (pullbackCongr (pullbackLeftPullbackSndIso_hom_fst f φ σ.hom)).app F ≪≫
    (pullbackCompIso (pullback.fst (pullback.snd f φ) σ.hom) (pullback.fst f φ)).symm.app F

/-- Transport to the original base and back fixes every morphism of the
base-changed modules. -/
theorem homFunctorBaseChangeEquiv_left_inv (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B') :
    Function.LeftInverse
      (fun v ↦
        (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
          (homFunctorBaseChangeModuleIsoInv f φ G σ)
          ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).hom).map v))
      (fun u ↦
        (homFunctorBaseChangeModuleIso f φ F σ).homCongr
          (homFunctorBaseChangeModuleIso f φ G σ)
          ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).map u)) :=
  sorry

/-- Transport to the changed base and back fixes every morphism of the
original base-changed modules. -/
theorem homFunctorBaseChangeEquiv_right_inv (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B') :
    Function.RightInverse
      (fun v ↦
        (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
          (homFunctorBaseChangeModuleIsoInv f φ G σ)
          ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).hom).map v))
      (fun u ↦
        (homFunctorBaseChangeModuleIso f φ F σ).homCongr
          (homFunctorBaseChangeModuleIso f φ G σ)
          ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).map u)) :=
  sorry

/-- Base change of the base algebraic space canonically identifies the Hom sets of
quasi-coherent modules at every scheme over the new base. -/
def homFunctorBaseChangeEquiv (f : X ⟶ B) (φ : B' ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B') :
    (homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G)).obj (op σ) ≃
      (homFunctor f F G).obj (op ((CostructuredArrow.map φ).obj σ)) where
  toFun u :=
    (homFunctorBaseChangeModuleIso f φ F σ).homCongr
      (homFunctorBaseChangeModuleIso f φ G σ)
      ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).map u)
  invFun v :=
    (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
      (homFunctorBaseChangeModuleIsoInv f φ G σ)
      ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).hom).map v)
  left_inv := homFunctorBaseChangeEquiv_left_inv f φ F G σ
  right_inv := homFunctorBaseChangeEquiv_right_inv f φ F G σ

/-- The forward base-change equivalence transports a morphism of
`𝒪_{X'_T}`-modules along the inverse pasting isomorphism and the module
comparison. -/
theorem homFunctorBaseChangeEquiv_apply (f : X ⟶ B) (φ : B' ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B')
    (u : (homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G)).obj (op σ)) :
    homFunctorBaseChangeEquiv f φ F G σ u =
      (homFunctorBaseChangeModuleIso f φ F σ).homCongr
        (homFunctorBaseChangeModuleIso f φ G σ)
        ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).inv).map u) :=
  rfl

/-- The inverse base-change equivalence transports a morphism of
`𝒪_{X_T}`-modules along the pasting isomorphism and the module comparison. -/
theorem homFunctorBaseChangeEquiv_symm_apply (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B')
    (v : (homFunctor f F G).obj (op ((CostructuredArrow.map φ).obj σ))) :
    (homFunctorBaseChangeEquiv f φ F G σ).symm v =
      (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
        (homFunctorBaseChangeModuleIsoInv f φ G σ)
        ((pullback (pullbackLeftPullbackSndIso f φ σ.hom).hom).map v) :=
  rfl

/-- As functors on `(SchemeOver B')ᵒᵖ`, `Hom(F', G')` is canonically isomorphic
to `Hom(F, G)` precomposed with viewing a scheme over `B'` as a scheme over `B`
via `φ`. -/
def homFunctor_baseChange (f : X ⟶ B) (φ : B' ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G) ≅
      (CostructuredArrow.map φ).op ⋙ homFunctor f F G :=
  NatIso.ofComponents
    (fun σ ↦ (homFunctorBaseChangeEquiv f φ F G σ.unop).toIso) sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
