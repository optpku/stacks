module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap67.Lemma_67_20_5_Pullback
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite
public import stacks_project.Chap69.Lemma_69_11_1_AffineBaseChange
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# Affine quasi-finite pushforward on the Grothendieck Quot functor

An affine quasi-finite morphism `π : X ⟶ Y` of algebraic spaces over `B`
induces a comparison `X_T ⟶ Y_T` on fibres. Affine base change identifies
`(π_* F)_T` with `π_{T,*} F_T`, and pushforward of a Quot-point of `F` along
this comparison yields a Quot-point of `π_* F`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `π : X ⟶ Y` over `B`. -/
def fiberComparison (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiber (π ≫ y) σ ⟶ fiber y σ :=
  pullback.map (π ≫ y) σ.hom y σ.hom π
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (π ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison commutes with the projections to `X` and `Y`. -/
theorem fiberComparison_fst (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
      pullback.fst (π ≫ y) σ.hom ≫ π :=
  sorry

/-- The fibre comparison is the map of pullbacks induced by `π` and the identity
on the test scheme. -/
theorem fiberComparison_spec (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
        pullback.fst (π ≫ y) σ.hom ≫ π ∧
      fiberComparison π y σ ≫ pullback.snd y σ.hom =
        pullback.snd (π ≫ y) σ.hom :=
  sorry

/-- The square relating `X_T ⟶ X` to `Y_T ⟶ Y` along `π` is cartesian. -/
theorem fiberComparison_isPullback_fst (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) :
    IsPullback (pullback.fst (π ≫ y) σ.hom) (fiberComparison π y σ)
      π (pullback.fst y σ.hom) :=
  sorry

/-- Fibrewise base change of an affine morphism `π` remains affine. -/
instance instAffine_fiberComparison (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) [Affine π] :
    Affine (fiberComparison π y σ) :=
  Affine.of_isPullback (fiberComparison_isPullback_fst π y σ) inferInstance

/-- The underived affine base-change mate
`(π_* F)_T ⟶ π_{T,*} F_T` associated to the cartesian fibre square. -/
def affineFiberBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B)
    (F : X.Modules) :
    fiberF y ((Modules.pushforward π).obj F) σ ⟶
      (Modules.pushforward (fiberComparison π y σ)).obj
        (fiberF (π ≫ y) F σ) :=
  (CategoryTheory.DerivedBaseChange.map
      (Modules.pullbackPushforwardAdjunction π)
      (Modules.pullbackPushforwardAdjunction (fiberComparison π y σ))
      (Modules.pullbackComp (fiberComparison π y σ) (pullback.fst y σ.hom) ≪≫
        eqToIso (congrArg Modules.pullback (pullback.lift_fst _ _ _)) ≪≫
        (Modules.pullbackComp (pullback.fst (π ≫ y) σ.hom) π).symm)).app F

/-- Affine base change identifies `(π_* F)_T` with `π_{T,*} F_T`. -/
instance instIsIso_affineFiberBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    IsIso (affineFiberBaseChangeHom π y σ F) :=
  sorry

/-- The canonical identification `(π_* F)_T ≅ π_{T,*} F_T`. -/
def affineFiberBaseChangeIso (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B)
    (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    fiberF y ((Modules.pushforward π).obj F) σ ≅
      (Modules.pushforward (fiberComparison π y σ)).obj
        (fiberF (π ≫ y) F σ) :=
  asIso (affineFiberBaseChangeHom π y σ F)

/-- The forward map of `affineFiberBaseChangeIso` is the underived affine
base-change mate. -/
theorem affineFiberBaseChangeIso_hom (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemesOver B) (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    (affineFiberBaseChangeIso π y σ F).hom =
      affineFiberBaseChangeHom π y σ F :=
  sorry

/-- Pushforward of a Quot-point `F_T ⟶ Q` along `π_T` yields a Quot-point
`(π_* F)_T ⟶ π_{T,*} Q`. -/
def QuotPoint.pushforward (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemesOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    QuotPoint y ((Modules.pushforward π).obj F) σ :=
  QuotPoint.ofEpi y ((Modules.pushforward π).obj F) σ
    ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module)
    ((affineFiberBaseChangeIso π y σ F).hom ≫
      (Modules.pushforward (fiberComparison π y σ)).map Q.point.map)
    sorry sorry sorry sorry sorry

/-- The underlying module of a pushed Quot-point is `π_{T,*} Q`. -/
theorem QuotPoint.pushforward_module (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemesOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (QuotPoint.pushforward π y Q).point.module =
      (Modules.pushforward (fiberComparison π y σ)).obj Q.point.module :=
  sorry

/-- The quotient map of a pushed Quot-point is the affine identification
`(π_* F)_T ≅ π_{T,*} F_T` followed by `π_{T,*} (F_T ⟶ Q)`. -/
theorem QuotPoint.pushforward_map (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemesOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (QuotPoint.pushforward π y Q).point.map =
      (affineFiberBaseChangeIso π y σ F).hom ≫
        (Modules.pushforward (fiberComparison π y σ)).map Q.point.map :=
  sorry

/-- A pushed Quot-point is the epimorphism `(π_* F)_T ⟶ π_{T,*} Q` obtained from
`F_T ⟶ Q` by affine base change and `π_{T,*}`. -/
theorem QuotPoint.pushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemesOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (QuotPoint.pushforward π y Q).point.module =
        (Modules.pushforward (fiberComparison π y σ)).obj Q.point.module ∧
      (QuotPoint.pushforward π y Q).point.map =
        (affineFiberBaseChangeIso π y σ F).hom ≫
          (Modules.pushforward (fiberComparison π y σ)).map Q.point.map :=
  sorry

/-- Kernel identification is preserved by fibrewise pushforward of Quot-points. -/
theorem Rel_pushforward (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent]
    (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint (π ≫ y) F σ),
      (quotSetoid (π ≫ y) F σ).r Q₁ Q₂ →
        (quotSetoid y ((Modules.pushforward π).obj F) σ).r
          (QuotPoint.pushforward π y Q₁) (QuotPoint.pushforward π y Q₂) :=
  sorry

/-- The natural transformation `Quot_{F/X/B} ⟶ Quot_{π_* F / Y/B}` induced by
fibrewise affine pushforward. -/
def pushforwardHom (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent] :
    quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F) where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map
        (fun Q : QuotPoint (π ≫ y) F σ.unop ↦ QuotPoint.pushforward π y Q)
        (Rel_pushforward π y F σ.unop))
  naturality := sorry

/-- The component of `pushforwardHom` at a test scheme is the setoid quotient
map of `QuotPoint.pushforward`. -/
theorem pushforwardHom_app (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent]
    (σ : (SchemesOver B)ᵒᵖ) :
    (pushforwardHom π y F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun Q : QuotPoint (π ≫ y) F σ.unop ↦ QuotPoint.pushforward π y Q)
          (Rel_pushforward π y F σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
