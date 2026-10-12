/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap99.«99_3_1_1»

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

/-- The pasting isomorphism `(X ×_B B') ×_{B'} T ≅ X ×_B T` identifying the
fibre product of `X'` with a scheme `T` over `B'` and the fibre product of `X`
with `T` viewed as a scheme over `B` via `T ⟶ B' ⟶ B`. -/
def homFunctorBaseChangeSpaceIso (f : X ⟶ B) (φ : B' ⟶ B) (σ : SchemeOver B') :
    baseChangeSpace (pullback.snd f φ) σ.hom ≅
      baseChangeSpace f ((CostructuredArrow.map φ).obj σ).hom :=
  pullbackLeftPullbackSndIso f φ σ.hom

/-- Pullback of `F'_T` along the inverse pasting isomorphism is identified with
`F_T`. -/
def homFunctorBaseChangeModuleIso (f : X ⟶ B) (φ : B' ⟶ B) (F : X.Modules)
    (σ : SchemeOver B') :
    (pullback (homFunctorBaseChangeSpaceIso f φ σ).inv).obj
        (baseChangeModule (pullback.snd f φ) σ.hom
          ((pullback (pullback.fst f φ)).obj F)) ≅
      baseChangeModule f ((CostructuredArrow.map φ).obj σ).hom F :=
  (pullback (homFunctorBaseChangeSpaceIso f φ σ).inv).mapIso
      ((pullbackComp (pullback.fst (pullback.snd f φ) σ.hom) (pullback.fst f φ)).app F) ≪≫
    (pullbackComp (homFunctorBaseChangeSpaceIso f φ σ).inv
        (pullback.fst (pullback.snd f φ) σ.hom ≫ pullback.fst f φ)).app F ≪≫
    (pullbackCongr (pullbackLeftPullbackSndIso_inv_fst f φ σ.hom)).app F

/-- Pullback of `F_T` along the pasting isomorphism is identified with `F'_T`. -/
def homFunctorBaseChangeModuleIsoInv (f : X ⟶ B) (φ : B' ⟶ B) (F : X.Modules)
    (σ : SchemeOver B') :
    (pullback (homFunctorBaseChangeSpaceIso f φ σ).hom).obj
        (baseChangeModule f ((CostructuredArrow.map φ).obj σ).hom F) ≅
      baseChangeModule (pullback.snd f φ) σ.hom
        ((pullback (pullback.fst f φ)).obj F) :=
  (pullbackComp (homFunctorBaseChangeSpaceIso f φ σ).hom
        (pullback.fst f ((CostructuredArrow.map φ).obj σ).hom)).app F ≪≫
    (pullbackCongr (pullbackLeftPullbackSndIso_hom_fst f φ σ.hom)).app F ≪≫
    (pullbackComp (pullback.fst (pullback.snd f φ) σ.hom) (pullback.fst f φ)).symm.app F

/-- Remark 99.3.4: in Situation 99.3.1, for a morphism `φ : B' ⟶ B` of algebraic
spaces over `S`, set `X' = X ×_B B'` and write `F'`, `G'` for the pullbacks of
`F`, `G` to `X'`. The Hom functor of `(f' : X' ⟶ B', F', G')` on schemes over
`B'` satisfies `Hom(F', G')(T) ≃ Hom(F, G)(T)` when a scheme `T` over `B'` is
viewed as a scheme over `B` via `T ⟶ B' ⟶ B`. -/
@[stacks 08JW]
def homFunctorBaseChangeEquiv (f : X ⟶ B) (φ : B' ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B') :
    (homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G)).obj (op σ) ≃
      (homFunctor f F G).obj (op ((CostructuredArrow.map φ).obj σ)) where
  toFun u :=
    (homFunctorBaseChangeModuleIso f φ F σ).homCongr
      (homFunctorBaseChangeModuleIso f φ G σ)
      ((pullback (homFunctorBaseChangeSpaceIso f φ σ).inv).map u)
  invFun v :=
    (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
      (homFunctorBaseChangeModuleIsoInv f φ G σ)
      ((pullback (homFunctorBaseChangeSpaceIso f φ σ).hom).map v)
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `homFunctorBaseChangeEquiv` transports a morphism of
`𝒪_{X'_T}`-modules along the inverse pasting isomorphism and the module
comparison. -/
theorem homFunctorBaseChangeEquiv_apply (f : X ⟶ B) (φ : B' ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B')
    (u : (homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G)).obj (op σ)) :
    homFunctorBaseChangeEquiv f φ F G σ u =
      (homFunctorBaseChangeModuleIso f φ F σ).homCongr
        (homFunctorBaseChangeModuleIso f φ G σ)
        ((pullback (homFunctorBaseChangeSpaceIso f φ σ).inv).map u) :=
  sorry

/-- The inverse map of `homFunctorBaseChangeEquiv` transports a morphism of
`𝒪_{X_T}`-modules along the pasting isomorphism and the module comparison. -/
theorem homFunctorBaseChangeEquiv_symm_apply (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B')
    (v : (homFunctor f F G).obj (op ((CostructuredArrow.map φ).obj σ))) :
    (homFunctorBaseChangeEquiv f φ F G σ).symm v =
      (homFunctorBaseChangeModuleIsoInv f φ F σ).homCongr
        (homFunctorBaseChangeModuleIsoInv f φ G σ)
        ((pullback (homFunctorBaseChangeSpaceIso f φ σ).hom).map v) :=
  sorry

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
