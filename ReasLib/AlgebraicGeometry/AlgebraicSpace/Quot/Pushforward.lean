module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FiberComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.AffineBaseChange

/-!
# Affine quasi-finite pushforward on the proper-support Quot functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The canonical module base-change comparison
`(π_* F)_T ⟶ π_{T,*} F_T` associated to the cartesian fibre square. -/
def affineFiberBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B)
    (F : X.Modules) :
    fiberF y ((Modules.pushforward π).obj F) σ ⟶
      (Modules.pushforward (fiberComparison π y σ)).obj
        (fiberF (π ≫ y) F σ) :=
  (Modules.baseChange (fiberComparison_isPullback_fst π y σ).w).app F

/-- Affine base change identifies `(π_* F)_T` with `π_{T,*} F_T`. -/
instance isIso_affineFiberBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    IsIso (affineFiberBaseChangeHom π y σ F) :=
  Modules.isIso_baseChange_of_affine (pullback.fst (π ≫ y) σ.hom)
    (fiberComparison π y σ) π (pullback.fst y σ.hom)
    (fiberComparison_isPullback_fst π y σ) F

/-- The canonical identification `(π_* F)_T ≅ π_{T,*} F_T`. -/
def affineFiberBaseChangeIso (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemeOver B)
    (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    fiberF y ((Modules.pushforward π).obj F) σ ≅
      (Modules.pushforward (fiberComparison π y σ)).obj
        (fiberF (π ≫ y) F σ) :=
  asIso (affineFiberBaseChangeHom π y σ F)

/-- The forward map of `affineFiberBaseChangeIso` is the canonical module
base-change comparison. -/
theorem affineFiberBaseChangeIso_hom (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B) (F : X.Modules) [Affine π] [F.IsQuasicoherent] :
    (affineFiberBaseChangeIso π y σ F).hom =
      affineFiberBaseChangeHom π y σ F :=
  sorry

namespace QuotPoint

/-- Fibrewise affine quasi-finite pushforward preserves epimorphisms, quasi-coherence,
flatness, finite presentation, and proper support for Quot-points. -/
private theorem pushforward_properties (π : X ⟶ Y) (y : Y ⟶ B)
    {F : X.Modules} {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    Epi ((affineFiberBaseChangeIso π y σ F).hom ≫
        (Modules.pushforward (fiberComparison π y σ)).map Q.point.map) ∧
      ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module).IsQuasicoherent ∧
      Modules.flatOver ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module)
        (pullback.snd y σ.hom) ∧
      ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module).IsFinitePresentation ∧
      supportProperOver (pullback.snd y σ.hom)
        ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module) := sorry

/-- Pushforward of a Quot-point `F_T ⟶ Q` along `π_T` yields a Quot-point
`(π_* F)_T ⟶ π_{T,*} Q`. -/
def pushforward (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    QuotPoint y ((Modules.pushforward π).obj F) σ :=
  QuotPoint.ofEpi y ((Modules.pushforward π).obj F) σ
    ((Modules.pushforward (fiberComparison π y σ)).obj Q.point.module)
    ((affineFiberBaseChangeIso π y σ F).hom ≫
      (Modules.pushforward (fiberComparison π y σ)).map Q.point.map)
    (by exact (pushforward_properties π y Q).1)
    (by exact (pushforward_properties π y Q).2.1)
    (by exact (pushforward_properties π y Q).2.2.1)
    (by exact (pushforward_properties π y Q).2.2.2.1)
    (by exact (pushforward_properties π y Q).2.2.2.2)

/-- The underlying module of a pushed Quot-point is `π_{T,*} Q`. -/
theorem pushforward_module (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (pushforward π y Q).point.module =
      (Modules.pushforward (fiberComparison π y σ)).obj Q.point.module :=
  sorry

/-- The quotient map of a pushed Quot-point is the affine identification
`(π_* F)_T ≅ π_{T,*} F_T` followed by `π_{T,*} (F_T ⟶ Q)`. -/
theorem pushforward_map (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (pushforward π y Q).point.map =
      (affineFiberBaseChangeIso π y σ F).hom ≫
        (Modules.pushforward (fiberComparison π y σ)).map Q.point.map :=
  sorry

/-- A pushed Quot-point is the epimorphism `(π_* F)_T ⟶ π_{T,*} Q` obtained from
`F_T ⟶ Q` by affine base change and `π_{T,*}`. -/
theorem pushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) {F : X.Modules}
    {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent]
    (Q : QuotPoint (π ≫ y) F σ) :
    (pushforward π y Q).point.module =
        (Modules.pushforward (fiberComparison π y σ)).obj Q.point.module ∧
      (pushforward π y Q).point.map =
        (affineFiberBaseChangeIso π y σ F).hom ≫
          (Modules.pushforward (fiberComparison π y σ)).map Q.point.map :=
  sorry

end QuotPoint

/-- Kernel identification is preserved by fibrewise pushforward of Quot-points. -/
theorem rel_pushforward (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent]
    (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : QuotPoint (π ≫ y) F σ),
      (quotSetoid (π ≫ y) F σ).r Q₁ Q₂ →
        (quotSetoid y ((Modules.pushforward π).obj F) σ).r
          (QuotPoint.pushforward π y Q₁) (QuotPoint.pushforward π y Q₂) :=
  sorry

/-- The natural transformation `Quot_{F/X/B} ⟶ Quot_{π_* F / Y/B}` induced by
fibrewise affine pushforward. -/
def map (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent] :
    quot (π ≫ y) F ⟶ quot y ((Modules.pushforward π).obj F) where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map
        (fun Q : QuotPoint (π ≫ y) F σ.unop ↦ QuotPoint.pushforward π y Q)
        (rel_pushforward π y F σ.unop))
  naturality := sorry

/-- The component of `map` at a test scheme is the setoid quotient
map of `QuotPoint.pushforward`. -/
theorem map_app (π : X ⟶ Y) (y : Y ⟶ B) (F : X.Modules)
    [Affine π] [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] [F.IsQuasicoherent]
    (σ : (SchemeOver B)ᵒᵖ) :
    (map π y F).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map
          (fun Q : QuotPoint (π ≫ y) F σ.unop ↦ QuotPoint.pushforward π y Q)
          (rel_pushforward π y F σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
