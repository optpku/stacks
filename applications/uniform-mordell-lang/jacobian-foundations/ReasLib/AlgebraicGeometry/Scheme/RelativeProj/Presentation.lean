module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.AffineOpenBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations of relative projective spectra

This file packages affine-local presentations of a scheme morphism by projective spectra of
graded rings over affine base rings.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- An explicit graded-ring model over an affine base ring. -/
structure AbsoluteProjModel where
  /-- The affine base ring. -/
  baseRing : CommRingCat.{u}
  /-- The ambient commutative graded ring. -/
  ring : CommRingCat.{u}
  /-- The type of graded pieces in the ambient ring. -/
  grade : Type u
  /-- Each graded piece is a subset of the ambient ring. -/
  gradeSetLike : SetLike grade ring
  /-- The graded pieces are additive subgroups of the ambient ring. -/
  gradeAddSubgroupClass : AddSubgroupClass grade ring
  /-- The nonnegative grading of the ambient ring. -/
  grading : ℕ → grade
  /-- The grading is multiplicative and decomposes the ambient ring. -/
  grading_inst : GradedRing grading
  /-- The ring map from the affine base ring to the ambient graded ring. -/
  baseToRing : baseRing ⟶ ring
  /-- The image of the affine base ring lies in degree zero. -/
  baseToRing_mem_zero : ∀ r : baseRing, baseToRing r ∈ grading 0

namespace AbsoluteProjModel

/-- The degree-zero component of an explicit graded-ring model, as a commutative ring. -/
def degreeZeroRing (D : AbsoluteProjModel) : CommRingCat.{u} :=
  @CommRingCat.of
    { x : D.ring //
      x ∈ @SetLike.coe D.grade D.ring D.gradeSetLike (D.grading 0) }
    (@SetLike.GradeZero.instCommRing ℕ D.grade D.ring D.ring.commRing inferInstance
      D.gradeSetLike D.gradeAddSubgroupClass D.grading D.grading_inst.toGradedMonoid)

/-- The projective spectrum of an explicit affine graded-ring model. -/
def proj (D : AbsoluteProjModel) : Scheme.{u} :=
  @AlgebraicGeometry.Proj D.ring D.grade D.ring.commRing D.gradeSetLike
    D.gradeAddSubgroupClass D.grading D.grading_inst

/-- The spectrum of the degree-zero component of an explicit graded-ring model. -/
def specZero (D : AbsoluteProjModel) : Scheme.{u} :=
  AlgebraicGeometry.Spec D.degreeZeroRing

/-- The canonical morphism from the projective spectrum to the degree-zero spectrum. -/
def toSpecZero (D : AbsoluteProjModel) : D.proj ⟶ D.specZero :=
  @AlgebraicGeometry.Proj.toSpecZero D.grade D.ring D.ring.commRing D.gradeSetLike
    D.gradeAddSubgroupClass D.grading D.grading_inst

/-- The spectrum of the affine base ring of an explicit graded-ring model. -/
def specBase (D : AbsoluteProjModel) : Scheme.{u} :=
  AlgebraicGeometry.Spec D.baseRing

/-- The ring map from the affine base ring to the degree-zero component. -/
def baseToZero (D : AbsoluteProjModel) : D.baseRing ⟶ D.degreeZeroRing :=
  @CommRingCat.ofHom D.baseRing D.degreeZeroRing
    D.baseRing.commRing D.degreeZeroRing.commRing
    { toFun := fun r ↦ ⟨D.baseToRing r, D.baseToRing_mem_zero r⟩
      map_one' := Subtype.ext D.baseToRing.hom.map_one
      map_mul' := fun x y ↦ Subtype.ext (D.baseToRing.hom.map_mul x y)
      map_zero' := Subtype.ext D.baseToRing.hom.map_zero
      map_add' := fun x y ↦ Subtype.ext (D.baseToRing.hom.map_add x y) }

/-- The structural morphism from the projective spectrum to the affine base spectrum. -/
def toSpecBase (D : AbsoluteProjModel) : D.proj ⟶ D.specBase :=
  D.toSpecZero ≫ AlgebraicGeometry.Spec.map D.baseToZero

/-- The structural morphism of an explicit affine projective-spectrum model is separated. -/
theorem isSeparated_toSpecBase (D : AbsoluteProjModel) :
    IsSeparated D.toSpecBase := sorry

end AbsoluteProjModel

/-- An affine-local identification of a scheme morphism with the projective spectrum of an
explicit graded-ring model over the affine base. -/
structure RelativeProjAffineChartAt
    (p : X ⟶ S)
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
      (AlgebraicGeometry.Scheme.schemeCommRingSheaf S))
    (s : S) where
  /-- An affine neighbourhood of the chosen point in the base. -/
  baseOpen : S.affineOpens
  /-- The affine neighbourhood contains the chosen point. -/
  mem_baseOpen : s ∈ (baseOpen : S.Opens)
  /-- The graded-ring model over the affine base. -/
  affineAlgebra : AbsoluteProjModel
  /-- The inverse image of the affine base is identified with the projective spectrum of the
  graded-ring model. -/
  sourceIso : (p ⁻¹ᵁ (baseOpen : S.Opens)).toScheme ≅ affineAlgebra.proj
  /-- The affine base is identified with the spectrum of the model's base ring. -/
  targetIso : (baseOpen : S.Opens).toScheme ≅ affineAlgebra.specBase
  /-- Under the chosen identifications, the restricted morphism agrees with the projective
  spectrum's structural morphism to the affine base. -/
  localProj_comm :
    sourceIso.hom ≫ affineAlgebra.toSpecBase =
      (p ∣_ (baseOpen : S.Opens)) ≫ targetIso.hom
  /-- On the affine base, each nonnegative graded piece agrees with the corresponding piece of
  the explicit graded-ring model. -/
  degreePieceSectionsIso :
    ∀ d : ℕ,
      @AddEquiv
        ((𝒜.obj (Int.ofNat d)).val.obj (Opposite.op (baseOpen : S.Opens)))
        { x : affineAlgebra.ring //
          x ∈ @SetLike.coe affineAlgebra.grade affineAlgebra.ring
            affineAlgebra.gradeSetLike (affineAlgebra.grading d) }
        inferInstance
        (@AddMemClass.add affineAlgebra.ring affineAlgebra.grade inferInstance
          affineAlgebra.gradeSetLike
          affineAlgebra.gradeAddSubgroupClass.toAddMemClass
          (affineAlgebra.grading d))
  /-- The degreewise additive identifications preserve the graded unit and homogeneous
  multiplication. -/
  isAffineOpenSectionModel :
    @AffineOpenSectionProj.IsAffineOpenSectionModel
      S affineAlgebra.ring affineAlgebra.grade affineAlgebra.ring.commRing
      affineAlgebra.gradeSetLike affineAlgebra.gradeAddSubgroupClass
      affineAlgebra.grading affineAlgebra.grading_inst 𝒜 baseOpen
      degreePieceSectionsIso

namespace RelativeProjAffineChartAt

variable
  {A : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
    (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)}
  {s : S}

/-- The morphism from the source of an affine chart to the spectrum of its model's base ring,
expressed in the projective-spectrum coordinates of the chart. -/
def modelMorphism (C : RelativeProjAffineChartAt p A s) :
    (p ⁻¹ᵁ (C.baseOpen : S.Opens)).toScheme ⟶ C.affineAlgebra.specBase :=
  C.sourceIso.hom ≫ C.affineAlgebra.toSpecBase

/-- The model-coordinate morphism of an affine chart agrees with the restricted morphism
followed by the chart's target identification. -/
theorem modelMorphism_eq (C : RelativeProjAffineChartAt p A s) :
    C.modelMorphism = (p ∣_ (C.baseOpen : S.Opens)) ≫ C.targetIso.hom :=
  C.localProj_comm

/-- The restriction of a relatively presented projective-spectrum morphism to one of its
affine base charts is separated. -/
theorem isSeparated_restrict (C : RelativeProjAffineChartAt p A s) :
    IsSeparated (p ∣_ (C.baseOpen : S.Opens)) := sorry

end RelativeProjAffineChartAt

/-- A presentation of a scheme morphism as a relative projective spectrum, including its graded
algebra, twists, and compatible affine-local projective-spectrum models. -/
@[stacks 01O2 "relative projective-spectrum presentation"]
structure RelativeProjPresentation (p : X ⟶ S) where
  /-- The graded algebra sheaf represented by the relative projective spectrum. -/
  algebra : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
    (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)
  /-- Every integer-graded piece of the algebra is quasi-coherent. -/
  algebra_isQuasicoherent : ∀ d : ℤ, (algebra.obj d).IsQuasicoherent
  /-- The family of twists on the source scheme. -/
  twist : ℤ → X.Modules
  /-- Every twist is quasi-coherent. -/
  twist_isQuasicoherent : ∀ d : ℤ, (twist d).IsQuasicoherent
  /-- The degree-zero twist is the structure sheaf of the source scheme. -/
  twist_zero : twist 0 ≅ SheafOfModules.unit X.ringCatSheaf
  /-- Compatible affine-local projective-spectrum models around every point of the base. -/
  affineChart : ∀ s : S, RelativeProjAffineChartAt p algebra s

namespace RelativeProjPresentation

/-- The nonnegative degree pieces of the graded algebra in a relative projective-spectrum
presentation. -/
@[stacks 01O2 "nonnegative degree piece of a relative projective-spectrum presentation"]
def degreePiece (P : RelativeProjPresentation p) (d : ℕ) : S.Modules :=
  P.algebra.obj (Int.ofNat d)

/-- Every nonnegative degree piece of a relative projective-spectrum presentation is
quasi-coherent. -/
@[stacks 01O2 "quasi-coherence of relative projective-spectrum degree pieces"]
theorem degreePiece_isQuasicoherent (P : RelativeProjPresentation p) (d : ℕ) :
    (P.degreePiece d).IsQuasicoherent :=
  P.algebra_isQuasicoherent (Int.ofNat d)

/-- The affine base charts in a relative projective-spectrum presentation cover the base
scheme. -/
theorem iSup_affineChart_eq_top (P : RelativeProjPresentation p) :
    ⨆ s : S, ((P.affineChart s).baseOpen : S.Opens) = ⊤ := sorry

/-- A morphism admitting a relative projective-spectrum presentation is separated. -/
@[stacks 01O2 "relative projective spectra are separated"]
theorem isSeparated (P : RelativeProjPresentation p) :
    IsSeparated p := sorry

end RelativeProjPresentation

end AlgebraicGeometry.Scheme.Hom
