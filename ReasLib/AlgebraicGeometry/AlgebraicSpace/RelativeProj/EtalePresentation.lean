/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.EtaleLocal
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.PartialGradedMap

/-! # Fixed affine-étale presentations of relative Proj and its integral twists -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X P Q R : AlgebraicSpace S}

/-- A fixed affine-étale section model and geometric identification of relative Proj,
with its actual integral Serre twisting modules. -/
structure EtalePresentation
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (π : P ⟶ X) (twist : ℤ → P.Modules) where
  /-- The commutative ring of each affine-étale section model. -/
  ring : affineEtaleSite X → CommRingCat.{u}
  /-- The nonnegative homogeneous pieces of the section ring. -/
  grading : ∀ U, ℕ → Submodule ℤ (ring U)
  /-- The section ring is the direct sum of its homogeneous pieces. -/
  graded : ∀ U, GradedAlgebra (grading U)
  /-- The degreewise identifications with the sections of the algebra. -/
  model : ∀ U d, (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+
    ULift.{u + 1} (grading U d)
  /-- The section identifications preserve the unit and multiplication. -/
  isModel : ∀ U, @IsEtaleSectionModel S X 𝒜 U.obj (ring U) inferInstance
    (grading U) (graded U) (model U)
  /-- The base-changed space is the actual projective spectrum of the section model. -/
  chartIso : ∀ U, etaleBaseChangeSpace π U.obj ≅
    ofOver (Over.mk (@etaleChartProj S X 𝒜 U (ring U) inferInstance
      (grading U) (graded U) (model U) (isModel U) ≫ U.obj.left.hom))
  /-- The geometric chart identification respects the structure map to the chart. -/
  chart_over : ∀ U, (chartIso U).hom ≫ ofOverMap
    (Over.homMk (@etaleChartProj S X 𝒜 U (ring U) inferInstance
      (grading U) (graded U) (model U) (isModel U)) rfl) = etaleBaseChangeSnd π U.obj
  /-- Each integral twist is identified with the actual homogeneous-fraction Serre sheaf. -/
  twistIso : ∀ U n, Modules.pullbackToScheme
    ((chartIso U).inv ≫ etaleBaseChangeHom π U.obj) (twist n) ≅
      @Proj.AssociatedModule.twistingSheaf ℤ (ring U) inferInstance inferInstance
        inferInstance (grading U) (graded U) n

namespace EtalePresentation

variable {𝒜 ℬ 𝒞 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {πP : P ⟶ X} {πQ : Q ⟶ X} {πR : R ⟶ X}
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules} {twistR : ℤ → R.Modules}

/-- The fixed projective-spectrum chart, as a scheme over the original base. -/
def chart (p : EtalePresentation 𝒜 πP twistP) (U : affineEtaleSite X) : Over S :=
  Over.mk (@etaleChartProj S X 𝒜 U (p.ring U) inferInstance (p.grading U)
    (p.graded U) (p.model U) (p.isModel U) ≫ U.obj.left.hom)

/-- The chart-to-space map is the inverse geometric identification followed by projection. -/
def chartMap (p : EtalePresentation 𝒜 πP twistP) (U : affineEtaleSite X) :
    ofOver (p.chart U) ⟶ P :=
  (p.chartIso U).inv ≫ etaleBaseChangeHom πP U.obj

/-- The canonical map from a projective chart to the affine-étale base scheme. -/
def chartBase (p : EtalePresentation 𝒜 πP twistP) (U : affineEtaleSite X) :
    (p.chart U).left ⟶ U.obj.left.left :=
  @etaleChartProj S X 𝒜 U (p.ring U) inferInstance (p.grading U)
    (p.graded U) (p.model U) (p.isModel U)

/-- The actual integral Serre twist on the fixed projective-spectrum chart. -/
abbrev serreTwist (p : EtalePresentation 𝒜 πP twistP) (U : affineEtaleSite X) (n : ℤ) :
    (p.chart U).left.Modules :=
  @Proj.AssociatedModule.twistingSheaf ℤ (p.ring U) inferInstance inferInstance
    inferInstance (p.grading U) (p.graded U) n

/-- Assemble a fixed presentation from its section, geometric, and Serre-twist identifications. -/
def ofCharts (ring : affineEtaleSite X → CommRingCat.{u})
    (grading : ∀ U, ℕ → Submodule ℤ (ring U)) (graded : ∀ U, GradedAlgebra (grading U))
    (model : ∀ U d, (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+
      ULift.{u + 1} (grading U d))
    (isModel : ∀ U, @IsEtaleSectionModel S X 𝒜 U.obj (ring U) inferInstance
      (grading U) (graded U) (model U))
    (chartIso : ∀ U, etaleBaseChangeSpace πP U.obj ≅
      ofOver (Over.mk (@etaleChartProj S X 𝒜 U (ring U) inferInstance
        (grading U) (graded U) (model U) (isModel U) ≫ U.obj.left.hom)))
    (chart_over) (twistIso) :=
  (⟨ring, grading, graded, model, isModel, chartIso, chart_over, twistIso⟩ :
    EtalePresentation 𝒜 πP twistP)

/-- The section models preserve unit and multiplication, and the geometric charts
and the Serre-twist identifications satisfy their defining compatibilities. -/
theorem spec (p : EtalePresentation 𝒜 πP twistP) (U : affineEtaleSite X) :
    @IsEtaleSectionModel S X 𝒜 U.obj (p.ring U) inferInstance
      (p.grading U) (p.graded U) (p.model U) ∧
    (p.chartIso U).hom ≫ ofOverMap (Over.homMk (p.chartBase U) rfl) =
      etaleBaseChangeSnd πP U.obj ∧
    ∀ n, (p.twistIso U n).hom ≫ (p.twistIso U n).inv = 𝟙 _ := sorry

/-- Integral twists identified étale-locally with Serre sheaves are quasi-coherent. -/
theorem twist_isQuasicoherent (p : EtalePresentation 𝒜 πP twistP) (n : ℤ) :
    (twistP n).IsQuasicoherent := sorry

/-- The scheme/algebraic-space composite-pullback comparison for an integral twist. -/
def twistCompositePullbackIso (p : EtalePresentation 𝒜 πP twistP)
    {T Z : Over S} (g : ofOver Z ⟶ P) (t : T ⟶ Z) (n : ℤ) :
    (Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj ((Modules.pullback g).obj (twistP n))) ≅
      (Modules.restrictToScheme T).obj
        ((Modules.pullback (ofOverMap t ≫ g)).obj (twistP n)) :=
  @Modules.RestrictToScheme.compositePullbackIso S P T Z g t (twistP n)
    (p.twist_isQuasicoherent n)

/-- The homogeneous section map transported through the fixed additive identifications. -/
def homComponent (p : EtalePresentation 𝒜 πP twistP)
    (q : EtalePresentation ℬ πQ twistQ) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (d : ℕ) (a : p.grading U d) : q.grading U d :=
  (q.model U d (((φ.hom (Int.ofNat d)).val.app (op U.obj)).hom
    ((p.model U d).symm (ULift.up a)))).down

/-- Extend the homogeneous section maps by the unique finite homogeneous decomposition. -/
def homFunction (p : EtalePresentation 𝒜 πP twistP)
    (q : EtalePresentation ℬ πQ twistQ) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (a : p.ring U) : q.ring U :=
  @DFinsupp.sum ℕ (q.ring U) (fun d ↦ p.grading U d) inferInstance inferInstance
    (fun _ _ ↦ Classical.propDecidable _) inferInstance
    (@DirectSum.decompose ℕ (p.ring U) (Submodule ℤ (p.ring U))
    inferInstance inferInstance inferInstance inferInstance
      (p.grading U) (p.graded U).toDecomposition a)
      (fun d x ↦ (p.homComponent q φ U d x).val)

/-- The finite homogeneous extension is a graded ring homomorphism. -/
theorem hom_laws (p : EtalePresentation 𝒜 πP twistP)
    (q : EtalePresentation ℬ πQ twistQ) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) :
    p.homFunction q φ U 1 = 1 ∧
    (∀ a b, p.homFunction q φ U (a * b) = p.homFunction q φ U a * p.homFunction q φ U b) ∧
    p.homFunction q φ U 0 = 0 ∧
    (∀ a b, p.homFunction q φ U (a + b) = p.homFunction q φ U a + p.homFunction q φ U b) ∧
    (∀ d a, a ∈ p.grading U d → p.homFunction q φ U a ∈ q.grading U d) := sorry

/-- The graded ring map induced by a map of graded algebra sheaves on an affine-étale chart. -/
def hom (p : EtalePresentation 𝒜 πP twistP) (q : EtalePresentation ℬ πQ twistQ)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) (U : affineEtaleSite X) :
    p.grading U →+*ᵍ q.grading U where
  toFun := p.homFunction q φ U
  map_one' := (p.hom_laws q φ U).1
  map_mul' := (p.hom_laws q φ U).2.1
  map_zero' := (p.hom_laws q φ U).2.2.1
  map_add' := (p.hom_laws q φ U).2.2.2.1
  map_mem := (p.hom_laws q φ U).2.2.2.2 _ _

/-- On homogeneous elements the induced ring map is the transported sheaf-section map. -/
theorem hom_apply (p : EtalePresentation 𝒜 πP twistP)
    (q : EtalePresentation ℬ πQ twistQ) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (d : ℕ) (a : p.grading U d) :
    p.hom q φ U a = (p.homComponent q φ U d a).val := sorry

/-- Induced graded ring maps commute with composition of sheaf-algebra homomorphisms. -/
theorem hom_comp (p : EtalePresentation 𝒜 πP twistP)
    (q : EtalePresentation ℬ πQ twistQ) (r : EtalePresentation 𝒞 πR twistR)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (U : affineEtaleSite X) :
    p.hom r (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ) U =
      (q.hom r ψ U).comp (p.hom q φ U) := sorry

end EtalePresentation
end AlgebraicGeometry.AlgebraicSpace.RelativeProj
