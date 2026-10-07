module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap71.Lemma_71_11_11_Triple

/-!
# Twists on the relative projective spectrum of an algebraic space

A twist presentation packages the algebraic space `P = underline{Proj}_X(𝒜)` in the sense of
Definition 71.11.3: an algebraic space over `X` whose base change along a surjective étale
atlas is a scheme, étale-locally the projective spectrum of a one-and-mul-preserving section
model of `𝒜`, together with the twists `𝒪_P(n)` identified with Serre twisting sheaves on
those charts, and the canonical graded map `π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The scheme over `S` obtained by viewing a Zariski open of an object of `X_étale` as an
open subscheme. -/
def openImmersionOver (U : smallEtaleSite X) (W : U.left.left.Opens) : Over S :=
  Over.mk (W.ι ≫ U.left.hom)

/-- The structure morphism of `openImmersionOver U W` is the open immersion followed by the
structure morphism of `U`. -/
theorem openImmersionOver_hom (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionOver U W).hom = W.ι ≫ U.left.hom :=
  sorry

/-- The open immersion of a Zariski open of `U`, as a morphism of schemes over `S`. -/
def openImmersionMap (U : smallEtaleSite X) (W : U.left.left.Opens) :
    openImmersionOver U W ⟶ U.left :=
  Over.homMk W.ι

/-- The underlying scheme morphism of `openImmersionMap U W` is the open immersion `W.ι`. -/
theorem openImmersionMap_left (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionMap U W).left = W.ι :=
  sorry

/-- The open immersion of a Zariski open of `U`, as a morphism of algebraic spaces over `S`. -/
def openImmersionι (U : smallEtaleSite X) (W : U.left.left.Opens) :
    ofOver (openImmersionOver U W) ⟶ ofOver U.left :=
  ofOverMap (openImmersionMap U W)

/-- `openImmersionι U W` is `ofOverMap` of the over-morphism induced by the open immersion. -/
theorem openImmersionι_eq (U : smallEtaleSite X) (W : U.left.left.Opens) :
    openImmersionι U W = ofOverMap (openImmersionMap U W) :=
  sorry

/-- The structure morphism of a Zariski open of `U` is étale as a morphism of algebraic
spaces into `X`. -/
instance etale_openImmersion_comp (U : smallEtaleSite X) (W : U.left.left.Opens) :
    Etale (openImmersionι U W ≫ U.hom) :=
  sorry

/-- The object of `X_étale` associated to a Zariski open of the underlying scheme of `U`. -/
def openImmersionSite (U : smallEtaleSite X) (W : U.left.left.Opens) : smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ (openImmersionι U W ≫ U.hom)
    (etale_openImmersion_comp U W)

/-- The structure morphism of `openImmersionSite U W` is the composite of the open immersion
with `U.hom`. -/
theorem openImmersionSite_hom (U : smallEtaleSite X) (W : U.left.left.Opens) :
    (openImmersionSite U W).hom = openImmersionι U W ≫ U.hom :=
  sorry

/-- `ℕ`-indexed integer-submodule grading of a commutative ring. -/
abbrev AtlasGrading (A : Type u) [CommRing A] : Type u :=
  ℕ → Submodule ℤ A

/-- `AtlasGrading A` is the type of maps `ℕ → Submodule ℤ A`. -/
theorem atlasGrading_eq (A : Type u) [CommRing A] :
    AtlasGrading A = (ℕ → Submodule ℤ A) :=
  rfl

/-- Graded-algebra structure on an atlas grading. -/
abbrev AtlasGradedAlgebra (A : Type u) [CommRing A] (grading : AtlasGrading A) :=
  GradedAlgebra grading

/-- `AtlasGradedAlgebra` is `GradedAlgebra` of the stored grading. -/
theorem atlasGradedAlgebra_eq (A : Type u) [CommRing A] (grading : AtlasGrading A) :
    AtlasGradedAlgebra A grading = GradedAlgebra grading :=
  rfl

/-- A graded ring homomorphism between atlas gradings, with ring instances supplied
explicitly from chart data. -/
def AtlasGradedRingHom {A B : Type u}
    (instA : CommRing A) (instB : CommRing B)
    (𝒜 : @AtlasGrading A instA) (ℬ : @AtlasGrading B instB) : Type u :=
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `CommRing` instance.
  letI := instA
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `CommRing` instance.
  letI := instB
  GradedRingHom 𝒜 ℬ

/-- The underlying function of an atlas graded ring homomorphism. -/
def AtlasGradedRingHom.applied {A B : Type u}
    (instA : CommRing A) (instB : CommRing B)
    {𝒜 : @AtlasGrading A instA} {ℬ : @AtlasGrading B instB}
    (f : AtlasGradedRingHom instA instB 𝒜 ℬ) (x : A) : B :=
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `CommRing` instance.
  letI := instA
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `CommRing` instance.
  letI := instB
  let f' : GradedRingHom 𝒜 ℬ := f
  f'.toFun x

/-- `AtlasGradedRingHom.applied instA instB f` is the underlying map of `f`. -/
theorem AtlasGradedRingHom.applied_eq {A B : Type u}
    (instA : CommRing A) (instB : CommRing B)
    {𝒜 : @AtlasGrading A instA} {ℬ : @AtlasGrading B instB}
    (f : AtlasGradedRingHom instA instB 𝒜 ℬ) :
    AtlasGradedRingHom.applied instA instB f =
      AtlasGradedRingHom.applied instA instB f :=
  rfl

/-- The scheme `Proj` of an atlas grading. -/
abbrev atlasProj (A : Type u) [CommRing A] (grading : AtlasGrading A)
    [GradedAlgebra grading] : Scheme.{u} :=
  Proj grading

/-- `atlasProj` is the scheme `Proj` of the atlas grading. -/
theorem atlasProj_eq (A : Type u) [CommRing A] (grading : AtlasGrading A)
    [GradedAlgebra grading] : atlasProj A grading = Proj grading :=
  rfl

/-- Serre twisting sheaf on the projective spectrum of an atlas grading. -/
abbrev atlasSerreTwist (A : Type u) [CommRing A] (grading : AtlasGrading A)
    [GradedAlgebra grading] (n : ℤ) : (atlasProj A grading).Modules :=
  Proj.AssociatedModule.twistingSheaf grading n

/-- `atlasSerreTwist` is Serre's twisting sheaf on `atlasProj`. -/
theorem atlasSerreTwist_eq (A : Type u) [CommRing A] (grading : AtlasGrading A)
    [GradedAlgebra grading] (n : ℤ) :
    atlasSerreTwist A grading n =
      Proj.AssociatedModule.twistingSheaf grading n :=
  rfl

/-- Degree-one generation of an atlas grading over its degree-zero piece. -/
abbrev AtlasGeneratedByDegreeOne (A : Type u) [CommRing A] (grading : AtlasGrading A)
    [GradedAlgebra grading] : Prop :=
  GradedAlgebra.GeneratedBy grading 1

/-- Degree-one generation of an atlas grading is `GradedAlgebra.GeneratedBy` at `1`. -/
theorem atlasGeneratedByDegreeOne_iff (A : Type u) [CommRing A]
    (grading : AtlasGrading A) [GradedAlgebra grading] :
    AtlasGeneratedByDegreeOne A grading ↔ GradedAlgebra.GeneratedBy grading 1 :=
  Iff.rfl

/-- Homogeneous multiplication of atlas grading pieces, with ring and graded-algebra
instances supplied explicitly from chart data. -/
def atlasHomogeneousMul {A : Type u} (instCommRing : CommRing A)
    (grading : @AtlasGrading A instCommRing)
    (instGradedAlgebra : @AtlasGradedAlgebra A instCommRing grading)
    {i j : ℕ} (x : grading i) (y : grading j) : grading (i + j) :=
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `CommRing` instance.
  letI := instCommRing
  -- Local instance justification (noncanonical choice): chart rings are stored
  -- structure data rather than a unique global `GradedAlgebra` instance.
  letI := instGradedAlgebra
  (SetLike.gMul grading).mul x y

/-- `atlasHomogeneousMul` is homogeneous multiplication of the stored atlas grading. -/
theorem atlasHomogeneousMul_eq {A : Type u} (instCommRing : CommRing A)
    (grading : @AtlasGrading A instCommRing)
    (instGradedAlgebra : @AtlasGradedAlgebra A instCommRing grading)
    {i j : ℕ} (x : grading i) (y : grading j) :
    atlasHomogeneousMul instCommRing grading instGradedAlgebra x y =
      atlasHomogeneousMul instCommRing grading instGradedAlgebra x y :=
  rfl

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Affine-open identification of étale-local sections of a graded algebra sheaf with a
degree-one-generated `Type u` graded algebra, preserving the degree-zero unit and
homogeneous multiplication. -/
def IsAtlasAffineProjModel
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (U : smallEtaleSite X) {A : Type u}
    [CommRing A] (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U) ≃+ ULift.{u + 1} (grading d)) : Prop :=
  model 0 (𝒜.one (op U)) = ULift.up (1 : grading 0) ∧
    ∀ (d e : ℕ)
      (x : (𝒜 (Int.ofNat d)).val.obj (op U))
      (y : (𝒜 (Int.ofNat e)).val.obj (op U)),
      HEq
        (𝒜.mul (op U) (Int.ofNat d) (Int.ofNat e) x y)
        ((model (d + e)).symm
          (ULift.up ((SetLike.gMul grading).mul (model d x).down (model e y).down)))

/-- A compatible atlas section model carries the sheaf unit to the graded unit. -/
theorem IsAtlasAffineProjModel.one_eq
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {U : smallEtaleSite X} {A : Type u}
    [CommRing A] {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    {model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U) ≃+ ULift.{u + 1} (grading d)}
    (hModel : IsAtlasAffineProjModel 𝒜 U grading model) :
    model 0 (𝒜.one (op U)) = ULift.up (1 : grading 0) :=
  hModel.1

/-- A compatible atlas section model carries homogeneous sheaf multiplication to graded
multiplication of the model. -/
theorem IsAtlasAffineProjModel.mul_eq
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {U : smallEtaleSite X} {A : Type u}
    [CommRing A] {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    {model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U) ≃+ ULift.{u + 1} (grading d)}
    (hModel : IsAtlasAffineProjModel 𝒜 U grading model)
    (d e : ℕ)
    (x : (𝒜 (Int.ofNat d)).val.obj (op U))
    (y : (𝒜 (Int.ofNat e)).val.obj (op U)) :
    HEq
      (𝒜.mul (op U) (Int.ofNat d) (Int.ofNat e) x y)
      ((model (d + e)).symm
        (ULift.up ((SetLike.gMul grading).mul (model d x).down (model e y).down))) :=
  hModel.2 d e x y

/-- Affine-open projective-spectrum data for an étale chart of relative Proj. -/
structure AtlasAffineProjData
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) where
  /-- The affine section ring. -/
  A : Type u
  /-- Commutative ring structure on the affine section ring. -/
  instCommRing : CommRing A
  /-- The nonnegative grading by submodules. -/
  grading : @AtlasGrading A instCommRing
  /-- The grading is a graded algebra. -/
  instGradedAlgebra : @AtlasGradedAlgebra A instCommRing grading
  /-- Additive identification of sheaf sections with universe-lifted graded pieces. -/
  model : ∀ d : ℕ,
    (𝒜 (Int.ofNat d)).val.obj
        (op (openImmersionSite atlas (V : atlas.left.left.Opens))) ≃+
      ULift.{u + 1} (grading d)
  /-- The identification preserves the degree-zero unit and homogeneous multiplication. -/
  isModel :
    @IsAtlasAffineProjModel S X 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens))
      A instCommRing grading instGradedAlgebra model
  /-- The fibre of the local relative Proj over this affine open is the projective spectrum
  of the section model. -/
  projIso :
    CategoryTheory.Limits.pullback localπ (V : atlas.left.left.Opens).ι ≅
      @atlasProj A instCommRing grading instGradedAlgebra
  /-- The structure morphism from the affine `Proj` chart to the affine open. -/
  toAffineOpen :
    @atlasProj A instCommRing grading instGradedAlgebra ⟶
      (V : atlas.left.left.Opens).toScheme
  /-- The chart isomorphism lies over the affine open. -/
  projIso_over :
    projIso.hom ≫ toAffineOpen =
      CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι
  /-- The affine section model is generated as a degree-zero algebra by its degree-one
  piece. -/
  generatedByDegreeOne :
    @AtlasGeneratedByDegreeOne A instCommRing grading instGradedAlgebra

namespace AtlasAffineProjData

/-- Construct affine-open projective-spectrum data from a one-and-mul-preserving model,
the scheme isomorphism to `Proj`, and degree-one generation. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (A : Type u) (instCommRing : CommRing A)
    (grading : @AtlasGrading A instCommRing)
    (instGradedAlgebra : @AtlasGradedAlgebra A instCommRing grading)
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj
          (op (openImmersionSite atlas (V : atlas.left.left.Opens))) ≃+
        ULift.{u + 1} (grading d))
    (isModel :
      @IsAtlasAffineProjModel S X 𝒜
        (openImmersionSite atlas (V : atlas.left.left.Opens))
        A instCommRing grading instGradedAlgebra model)
    (projIso :
      CategoryTheory.Limits.pullback localπ (V : atlas.left.left.Opens).ι ≅
        @atlasProj A instCommRing grading instGradedAlgebra)
    (toAffineOpen :
      @atlasProj A instCommRing grading instGradedAlgebra ⟶
        (V : atlas.left.left.Opens).toScheme)
    (projIso_over :
      projIso.hom ≫ toAffineOpen =
        CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι)
    (generatedByDegreeOne :
      @AtlasGeneratedByDegreeOne A instCommRing grading instGradedAlgebra) :
    AtlasAffineProjData 𝒜 atlas localScheme localπ V where
  A := A
  instCommRing := instCommRing
  grading := grading
  instGradedAlgebra := instGradedAlgebra
  model := model
  isModel := isModel
  projIso := projIso
  toAffineOpen := toAffineOpen
  projIso_over := projIso_over
  generatedByDegreeOne := generatedByDegreeOne

/-- The stored affine model preserves unit and multiplication, and is generated in degree
one. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :
    @IsAtlasAffineProjModel S X 𝒜
        (openImmersionSite atlas (V : atlas.left.left.Opens))
        data.A data.instCommRing data.grading data.instGradedAlgebra data.model ∧
      data.projIso.hom ≫ data.toAffineOpen =
        CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι ∧
      @AtlasGeneratedByDegreeOne data.A data.instCommRing data.grading data.instGradedAlgebra :=
  ⟨data.isModel, data.projIso_over, data.generatedByDegreeOne⟩

/-- The fibre of the local relative Proj over this affine open is the projective spectrum of
the stored section model. -/
def projIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :
    CategoryTheory.Limits.pullback localπ (V : atlas.left.left.Opens).ι ≅
      @atlasProj data.A data.instCommRing data.grading data.instGradedAlgebra :=
  data.projIso

/-- Serre's twisting sheaf of index `n` on the affine projective spectrum of this chart. -/
def serreTwist {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) (n : ℤ) :
    (@atlasProj data.A data.instCommRing data.grading data.instGradedAlgebra).Modules :=
  @atlasSerreTwist data.A data.instCommRing data.grading data.instGradedAlgebra n

end AtlasAffineProjData

/-- The restriction arrow in `X_étale` associated to nested Zariski opens of an atlas chart. -/
def atlasOpenLe {S : Scheme.{u}} {X : AlgebraicSpace S}
    (atlas : smallEtaleSite X) {V V' : atlas.left.left.Opens} (h : V ≤ V') :
    openImmersionSite atlas V ⟶ openImmersionSite atlas V' :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.homOfLE atlas.left.left h) sorry) trivial sorry

/-- The fibre restriction of the local relative Proj over nested affine opens. -/
def atlasFibreRestrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {V V' : atlas.left.left.affineOpens}
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)) :
    CategoryTheory.Limits.pullback localπ (V : atlas.left.left.Opens).ι ⟶
      CategoryTheory.Limits.pullback localπ (V' : atlas.left.left.Opens).ι :=
  CategoryTheory.Limits.pullback.lift
    (CategoryTheory.Limits.pullback.fst localπ (V : atlas.left.left.Opens).ι)
    (CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι ≫
      Scheme.homOfLE atlas.left.left h) sorry

/-- The scheme underlying the étale cover of a twist presentation. -/
abbrev localCoverOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left) : Over S :=
  Over.mk (localπ ≫ atlas.left.hom)

/-- The fibre of the local relative Proj over an affine open of the atlas, as a scheme over
`S`. -/
def chartFibreOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) : Over S :=
  Over.mk
    (CategoryTheory.Limits.pullback.fst localπ (V : atlas.left.left.Opens).ι ≫
      localπ ≫ atlas.left.hom)

/-- `chartFibreOver` is the pullback of `localπ` along the affine open, viewed over `S`. -/
theorem chartFibreOver_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) :
    (chartFibreOver localπ V).hom =
      CategoryTheory.Limits.pullback.fst localπ (V : atlas.left.left.Opens).ι ≫
        localπ ≫ atlas.left.hom :=
  rfl

/-- The open immersion of the affine-chart fibre into the local relative Proj, as a morphism
of schemes over `S`. -/
def chartFibreOverHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) :
    chartFibreOver localπ V ⟶ localCoverOver atlas localScheme localπ :=
  Over.homMk
    (CategoryTheory.Limits.pullback.fst localπ (V : atlas.left.left.Opens).ι)

/-- The underlying scheme morphism of `chartFibreOverHom` is the pullback projection. -/
theorem chartFibreOverHom_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) :
    (chartFibreOverHom localπ V).left =
      CategoryTheory.Limits.pullback.fst localπ (V : atlas.left.left.Opens).ι :=
  rfl

/-- The covering morphism of an affine-chart fibre into the twist space. -/
def chartFibreCoverHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens) :
    ofOver (chartFibreOver localπ V) ⟶ space :=
  ofOverMap (chartFibreOverHom localπ V) ≫ localCoverHom

/-- `chartFibreCoverHom` is `ofOverMap` of the fibre inclusion followed by the local covering
morphism. -/
theorem chartFibreCoverHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens) :
    chartFibreCoverHom localπ localCoverHom V =
      ofOverMap (chartFibreOverHom localπ V) ≫ localCoverHom :=
  rfl

/-- Homogeneous degree-one elements of an affine chart model, as universe-unlifted sections of
`deg.obj 1` on the corresponding étale open. -/
def degreeOneUnliftedChartSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (f : data.grading 1) :
    (deg.obj 1).val.obj
      (op (openImmersionSite atlas (V : atlas.left.left.Opens))) :=
  (((deg.iso 1).inv.val.app
      (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
    ((data.model 1).symm (ULift.up f))).down

/-- `degreeOneUnliftedChartSection` is the universe-down of the inverse chart model. -/
theorem degreeOneUnliftedChartSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (f : data.grading 1) :
    degreeOneUnliftedChartSection deg data f =
      (((deg.iso 1).inv.val.app
          (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
        ((data.model 1).symm (ULift.up f))).down :=
  rfl

/-- Fibre restriction of a module on the twist space to an affine-chart fibre. -/
abbrev chartFibreRestrictModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens)
    (M : space.Modules) :
    (chartFibreOver localπ V).left.Modules :=
  (Modules.restrictToScheme (chartFibreOver localπ V)).obj
    ((Modules.pullback (chartFibreCoverHom localπ localCoverHom V)).obj M)

/-- `chartFibreRestrictModule` is restriction of the pulled-back module to the fibre scheme. -/
theorem chartFibreRestrictModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens)
    (M : space.Modules) :
    chartFibreRestrictModule localπ localCoverHom V M =
      (Modules.restrictToScheme (chartFibreOver localπ V)).obj
        ((Modules.pullback (chartFibreCoverHom localπ localCoverHom V)).obj M) :=
  rfl

/-- The fibre morphism `chartFibreCoverHom` is étale. -/
instance etale_chartFibreCoverHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens) :
    Etale (chartFibreCoverHom localπ localCoverHom V) :=
  sorry

/-- The affine-chart fibre as an object of the small étale site of the twist space. -/
def chartFibreSite {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens) : smallEtaleSite space :=
  smallEtaleSite.mk (chartFibreCoverHom localπ localCoverHom V)

/-- `chartFibreSite` is `smallEtaleSite.mk` of the fibre covering morphism. -/
theorem chartFibreSite_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (V : atlas.left.left.affineOpens) :
    chartFibreSite localπ localCoverHom V =
      smallEtaleSite.mk (chartFibreCoverHom localπ localCoverHom V) :=
  rfl

/-- Multiplication of fibre sections of `𝒪_P(n)` and `𝒪_P(m)` transported from
`twistAlgebra.mul` along `twistModuleIso`. -/
def chartFibreAlgebraMul {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space))
    (twistModule : ℤ → space.Modules)
    (twistModuleIso : ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n)
    (V : atlas.left.left.affineOpens) (n m : ℤ)
    (s : (Modules.liftModule (twistModule n)).val.obj
      (op (chartFibreSite localπ localCoverHom V)))
    (t : (Modules.liftModule (twistModule m)).val.obj
      (op (chartFibreSite localπ localCoverHom V))) :
    (Modules.liftModule (twistModule (n + m))).val.obj
      (op (chartFibreSite localπ localCoverHom V)) :=
  ((twistModuleIso (n + m)).inv.val.app
      (op (chartFibreSite localπ localCoverHom V))).hom
    (twistAlgebra.mul (op (chartFibreSite localπ localCoverHom V)) n m
      (((twistModuleIso n).hom.val.app
          (op (chartFibreSite localπ localCoverHom V))).hom s)
      (((twistModuleIso m).hom.val.app
          (op (chartFibreSite localπ localCoverHom V))).hom t))

/-- `chartFibreAlgebraMul` is `twistAlgebra.mul` after `twistModuleIso`. -/
theorem chartFibreAlgebraMul_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space))
    (twistModule : ℤ → space.Modules)
    (twistModuleIso : ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n)
    (V : atlas.left.left.affineOpens) (n m : ℤ)
    (s : (Modules.liftModule (twistModule n)).val.obj
      (op (chartFibreSite localπ localCoverHom V)))
    (t : (Modules.liftModule (twistModule m)).val.obj
      (op (chartFibreSite localπ localCoverHom V))) :
    chartFibreAlgebraMul localπ localCoverHom twistAlgebra twistModule twistModuleIso
        V n m s t =
      ((twistModuleIso (n + m)).inv.val.app
          (op (chartFibreSite localπ localCoverHom V))).hom
        (twistAlgebra.mul (op (chartFibreSite localπ localCoverHom V)) n m
          (((twistModuleIso n).hom.val.app
              (op (chartFibreSite localπ localCoverHom V))).hom s)
          (((twistModuleIso m).hom.val.app
              (op (chartFibreSite localπ localCoverHom V))).hom t)) :=
  rfl

/-- Transport of a degree-one chart-model section along the chart fibre of `π`, as the
adjunction-unit section of `π_* π^* 𝒜_1` on the affine chart open. -/
def chartFibreDegreeOneUnliftedSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {space : AlgebraicSpace S} (π : space ⟶ X)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (f : data.grading 1) :
    ((Modules.pushforward π).obj ((Modules.pullback π).obj (deg.obj 1))).val.obj
      (op (openImmersionSite atlas (V : atlas.left.left.Opens))) :=
  (((Modules.pullbackPushforwardAdjunction π).unit.app (deg.obj 1)).val.app
      (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
    (degreeOneUnliftedChartSection deg data f)

/-- `chartFibreDegreeOneUnliftedSection` is the adjunction-unit image of the unlifted
chart-model section. -/
theorem chartFibreDegreeOneUnliftedSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {space : AlgebraicSpace S} (π : space ⟶ X)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (f : data.grading 1) :
    chartFibreDegreeOneUnliftedSection deg π localπ localCoverHom data f =
      (((Modules.pullbackPushforwardAdjunction π).unit.app (deg.obj 1)).val.app
          (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
        (degreeOneUnliftedChartSection deg data f) :=
  rfl

/-- Serre's `twistSection` of a homogeneous chart-model element, transported along `projIso`
and `serreTwistIso` to a global section of the fibre restriction of `𝒪_P(n)`. -/
def chartFibreTransportedTwistSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (twistModule : ℤ → space.Modules)
    (localSectionData :
      ∀ V : atlas.left.left.affineOpens,
        AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (serreTwistIso :
      ∀ (V : atlas.left.left.affineOpens) (n : ℤ),
        (Scheme.Modules.pullback (localSectionData V).projIso.hom).obj
            (AtlasAffineProjData.serreTwist (localSectionData V) n) ≅
          chartFibreRestrictModule localπ localCoverHom V (twistModule n))
    (V : atlas.left.left.affineOpens) {n : ℕ}
    (f : (localSectionData V).grading n) :
    (chartFibreRestrictModule localπ localCoverHom V
      (twistModule (Int.ofNat n))).val.obj (op ⊤) :=
  ((serreTwistIso V (Int.ofNat n)).hom.val.app (op ⊤)).hom
    ((Scheme.Modules.globalSectionsPullback
        (localSectionData V).projIso.hom
        (AtlasAffineProjData.serreTwist (localSectionData V) (Int.ofNat n))).hom
      (@Proj.AssociatedModule.twistSection (localSectionData V).A
        (localSectionData V).instCommRing
        (localSectionData V).grading (localSectionData V).instGradedAlgebra
        (n := n) f))

/-- `chartFibreTransportedTwistSection` is `twistSection` after `projIso` and
`serreTwistIso`. -/
theorem chartFibreTransportedTwistSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (twistModule : ℤ → space.Modules)
    (localSectionData :
      ∀ V : atlas.left.left.affineOpens,
        AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (serreTwistIso :
      ∀ (V : atlas.left.left.affineOpens) (n : ℤ),
        (Scheme.Modules.pullback (localSectionData V).projIso.hom).obj
            (AtlasAffineProjData.serreTwist (localSectionData V) n) ≅
          chartFibreRestrictModule localπ localCoverHom V (twistModule n))
    (V : atlas.left.left.affineOpens) {n : ℕ}
    (f : (localSectionData V).grading n) :
    chartFibreTransportedTwistSection localπ localCoverHom twistModule
        localSectionData serreTwistIso V f =
      ((serreTwistIso V (Int.ofNat n)).hom.val.app (op ⊤)).hom
        ((Scheme.Modules.globalSectionsPullback
            (localSectionData V).projIso.hom
            (AtlasAffineProjData.serreTwist (localSectionData V)
              (Int.ofNat n))).hom
          (@Proj.AssociatedModule.twistSection (localSectionData V).A
            (localSectionData V).instCommRing
            (localSectionData V).grading (localSectionData V).instGradedAlgebra
            (n := n) f)) :=
  rfl

/-- A twist presentation of relative Proj of a graded algebra sheaf on an algebraic space,
forced to agree étale-locally with Serre twists on scheme-level `Proj`. -/
structure Twist {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) where
  /-- The algebraic space `P = underline{Proj}_X(𝒜)`. -/
  space : AlgebraicSpace S
  /-- The structure morphism `π : P ⟶ X`. -/
  π : space ⟶ X
  /-- The graded twist algebra whose degree-`n` piece is `𝒪_P(n)`. -/
  twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space)
  /-- The family of twist modules `𝒪_P(n)` on `P`. -/
  twistModule : ℤ → space.Modules
  /-- Universe lift identifies `𝒪_P(n)` with the degree-`n` piece of the twist algebra. -/
  twistModuleIso :
    ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n
  /-- Degreewise components of the canonical graded map `π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`. -/
  canonicalHom : ∀ n : ℕ,
    (Modules.pullback π).obj (deg.obj n) ⟶ twistModule n
  /-- The canonical map sends the pulled-back unit of `𝒜` to the unit of the twist
  algebra. -/
  canonicalHom_map_one :
    ∀ U : smallEtaleSite space,
      (((Modules.liftModuleMap (canonicalHom 0)).val.app (op U)).hom)
          (psiSourceOneSection π deg (op U)) =
        ((twistModuleIso 0).inv.val.app (op U)).hom (twistAlgebra.one (op U))
  /-- The canonical map preserves multiplication, compared with `twistAlgebra.mul`. -/
  canonicalHom_map_mul :
    ∀ (U : smallEtaleSite space) (i j : ℕ)
      (x : (psiSource π deg i).val.obj (op U))
      (y : (psiSource π deg j).val.obj (op U)),
      (((Modules.liftModuleMap (canonicalHom (i + j))).val.app (op U)).hom)
          (psiSourceMulSection π deg (op U) i j x y) =
        ((twistModuleIso (Int.ofNat (i + j))).inv.val.app (op U)).hom
          (twistAlgebra.mul (op U) (Int.ofNat i) (Int.ofNat j)
            (((twistModuleIso (Int.ofNat i)).hom.val.app (op U)).hom
              (((Modules.liftModuleMap (canonicalHom i)).val.app (op U)).hom x))
            (((twistModuleIso (Int.ofNat j)).hom.val.app (op U)).hom
              (((Modules.liftModuleMap (canonicalHom j)).val.app (op U)).hom y)))
  /-- A scheme étale over `X` providing the atlas of Definition 71.11.3. -/
  atlas : smallEtaleSite X
  /-- The atlas morphism is étale-locally surjective. -/
  atlas_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas.hom
  /-- The scheme `underline{Proj}_U(𝒜_U)` covering `P` étale-locally. -/
  localScheme : Scheme.{u}
  /-- The structure morphism of the local scheme relative Proj. -/
  localπ : localScheme ⟶ atlas.left.left
  /-- Base change of `P` along the atlas is the local scheme relative Proj. -/
  localIso :
    etaleBaseChangeSpace π atlas ≅ ofOver (localCoverOver atlas localScheme localπ)
  /-- The comparison identifies the projection to the atlas with the local structure
  morphism. -/
  localIso_snd :
    localIso.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas
  /-- The étale morphism `underline{Proj}_U(𝒜_U) ⟶ P` from the local scheme. -/
  localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space
  /-- The covering morphism is the base-change projection after the local identification. -/
  localCoverHom_eq :
    localCoverHom = localIso.inv ≫ etaleBaseChangeHom π atlas
  /-- On every affine open of the atlas, the local scheme fibre is the projective spectrum
  of a one-and-mul-preserving, degree-one-generated section model of `𝒜`. -/
  localSectionData :
    ∀ V : atlas.left.left.affineOpens,
      AtlasAffineProjData 𝒜 atlas localScheme localπ V
  /-- Restriction of `𝒪_P(n)` to each affine chart recovers Serre's twisting sheaf. -/
  serreTwistIso :
    ∀ (V : atlas.left.left.affineOpens) (n : ℤ),
      (Scheme.Modules.pullback (localSectionData V).projIso.hom).obj
          (AtlasAffineProjData.serreTwist (localSectionData V) n) ≅
        chartFibreRestrictModule localπ localCoverHom V (twistModule n)
  /-- Restriction of affine chart models along nested affine opens. -/
  sectionRestrict :
    ∀ (V V' : atlas.left.left.affineOpens),
      (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens) →
        AtlasGradedRingHom (localSectionData V').instCommRing
          (localSectionData V).instCommRing
          (localSectionData V').grading (localSectionData V).grading
  /-- Restriction of models recovers sheaf restriction on nested affine opens. -/
  sectionRestrict_spec :
    ∀ (V V' : atlas.left.left.affineOpens)
      (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens))
      (d : ℕ) (x : (localSectionData V').grading d),
      ((localSectionData V).model d
          (((𝒜 (Int.ofNat d)).val.map (atlasOpenLe atlas h).op).hom
            (((localSectionData V').model d).symm (ULift.up x)))).down =
        AtlasGradedRingHom.applied (localSectionData V').instCommRing
          (localSectionData V).instCommRing (sectionRestrict V V' h) x
  /-- The induced morphism of affine `Proj` charts along nested affine opens. -/
  chartRestrict :
    ∀ (V V' : atlas.left.left.affineOpens),
      (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens) →
        (@atlasProj (localSectionData V).A (localSectionData V).instCommRing
            (localSectionData V).grading (localSectionData V).instGradedAlgebra ⟶
          @atlasProj (localSectionData V').A (localSectionData V').instCommRing
            (localSectionData V').grading (localSectionData V').instGradedAlgebra)
  /-- Chart morphisms lie over the restriction of affine opens. -/
  chartRestrict_over :
    ∀ (V V' : atlas.left.left.affineOpens)
      (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)),
      (localSectionData V).toAffineOpen ≫ Scheme.homOfLE atlas.left.left h =
        chartRestrict V V' h ≫ (localSectionData V').toAffineOpen
  /-- Chart isomorphisms are compatible with fibre restriction. -/
  projIso_restrict :
    ∀ (V V' : atlas.left.left.affineOpens)
      (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)),
      (localSectionData V).projIso.hom ≫ chartRestrict V V' h =
        atlasFibreRestrict localπ h ≫ (localSectionData V').projIso.hom
  /-- On each affine chart, the adjunction-unit transport of the degree-one chart-model
  section, mapped by `π_* canonicalHom 1`, agrees with Serre's `twistSection` after
  `projIso` and `serreTwistIso`. -/
  canonicalHom_agrees_with_twistSection :
    ∀ (V : atlas.left.left.affineOpens)
      (f : (localSectionData V).grading 1),
      HEq
        ((((Modules.pushforward π).map (canonicalHom 1)).val.app
            (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
          (chartFibreDegreeOneUnliftedSection deg π localπ localCoverHom
            (localSectionData V) f))
        (((serreTwistIso V 1).hom.val.app (op ⊤)).hom
          ((Scheme.Modules.globalSectionsPullback
              (localSectionData V).projIso.hom
              (AtlasAffineProjData.serreTwist (localSectionData V) 1)).hom
            (@Proj.AssociatedModule.twistSection (localSectionData V).A
              (localSectionData V).instCommRing
              (localSectionData V).grading (localSectionData V).instGradedAlgebra
              (n := 1) f)))
  /-- After `twistModuleIso` and `serreTwistIso`, multiplication in `twistAlgebra` agrees
  with chartwise Serre multiplication of homogeneous chart-model sections. -/
  twistMul_agrees_with_serreMul :
    ∀ (V : atlas.left.left.affineOpens) (n m : ℕ)
      (x : (localSectionData V).grading n)
      (y : (localSectionData V).grading m),
      HEq
        (tensorSection (chartFibreOver localπ V).left.sheaf (op ⊤)
          (chartFibreTransportedTwistSection localπ localCoverHom twistModule
            localSectionData serreTwistIso V x)
          (chartFibreTransportedTwistSection localπ localCoverHom twistModule
            localSectionData serreTwistIso V y))
        (chartFibreTransportedTwistSection localπ localCoverHom twistModule
          localSectionData serreTwistIso V
          (atlasHomogeneousMul (localSectionData V).instCommRing
            (localSectionData V).grading (localSectionData V).instGradedAlgebra
            x y))

namespace Twist

/-- Construct a twist presentation from its space, structure morphism, twists, canonical
graded map, and étale-local Serre identification. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜}
    (space : AlgebraicSpace S) (π : space ⟶ X)
    (twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space))
    (twistModule : ℤ → space.Modules)
    (twistModuleIso : ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n)
    (canonicalHom : ∀ n : ℕ,
      (Modules.pullback π).obj (deg.obj n) ⟶ twistModule n)
    (canonicalHom_map_one :
      ∀ U : smallEtaleSite space,
        (((Modules.liftModuleMap (canonicalHom 0)).val.app (op U)).hom)
            (psiSourceOneSection π deg (op U)) =
          ((twistModuleIso 0).inv.val.app (op U)).hom (twistAlgebra.one (op U)))
    (canonicalHom_map_mul :
      ∀ (U : smallEtaleSite space) (i j : ℕ)
        (x : (psiSource π deg i).val.obj (op U))
        (y : (psiSource π deg j).val.obj (op U)),
        (((Modules.liftModuleMap (canonicalHom (i + j))).val.app (op U)).hom)
            (psiSourceMulSection π deg (op U) i j x y) =
          ((twistModuleIso (Int.ofNat (i + j))).inv.val.app (op U)).hom
            (twistAlgebra.mul (op U) (Int.ofNat i) (Int.ofNat j)
              (((twistModuleIso (Int.ofNat i)).hom.val.app (op U)).hom
                (((Modules.liftModuleMap (canonicalHom i)).val.app (op U)).hom x))
              (((twistModuleIso (Int.ofNat j)).hom.val.app (op U)).hom
                (((Modules.liftModuleMap (canonicalHom j)).val.app (op U)).hom y))))
    (atlas : smallEtaleSite X)
    (atlas_locallySurjective :
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas.hom)
    (localScheme : Scheme.{u}) (localπ : localScheme ⟶ atlas.left.left)
    (localIso : etaleBaseChangeSpace π atlas ≅
      ofOver (localCoverOver atlas localScheme localπ))
    (localIso_snd :
      localIso.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas)
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (localCoverHom_eq :
      localCoverHom = localIso.inv ≫ etaleBaseChangeHom π atlas)
    (localSectionData :
      ∀ V : atlas.left.left.affineOpens,
        AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    (serreTwistIso :
      ∀ (V : atlas.left.left.affineOpens) (n : ℤ),
        (Scheme.Modules.pullback (localSectionData V).projIso.hom).obj
            (AtlasAffineProjData.serreTwist (localSectionData V) n) ≅
          chartFibreRestrictModule localπ localCoverHom V (twistModule n))
    (sectionRestrict :
      ∀ (V V' : atlas.left.left.affineOpens),
        (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens) →
          AtlasGradedRingHom (localSectionData V').instCommRing
            (localSectionData V).instCommRing
            (localSectionData V').grading (localSectionData V).grading)
    (sectionRestrict_spec :
      ∀ (V V' : atlas.left.left.affineOpens)
        (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens))
        (d : ℕ) (x : (localSectionData V').grading d),
        ((localSectionData V).model d
            (((𝒜 (Int.ofNat d)).val.map (atlasOpenLe atlas h).op).hom
              (((localSectionData V').model d).symm (ULift.up x)))).down =
          AtlasGradedRingHom.applied (localSectionData V').instCommRing
            (localSectionData V).instCommRing (sectionRestrict V V' h) x)
    (chartRestrict :
      ∀ (V V' : atlas.left.left.affineOpens),
        (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens) →
          (@atlasProj (localSectionData V).A (localSectionData V).instCommRing
              (localSectionData V).grading (localSectionData V).instGradedAlgebra ⟶
            @atlasProj (localSectionData V').A (localSectionData V').instCommRing
              (localSectionData V').grading (localSectionData V').instGradedAlgebra))
    (chartRestrict_over :
      ∀ (V V' : atlas.left.left.affineOpens)
        (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)),
        (localSectionData V).toAffineOpen ≫ Scheme.homOfLE atlas.left.left h =
          chartRestrict V V' h ≫ (localSectionData V').toAffineOpen)
    (projIso_restrict :
      ∀ (V V' : atlas.left.left.affineOpens)
        (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)),
        (localSectionData V).projIso.hom ≫ chartRestrict V V' h =
          atlasFibreRestrict localπ h ≫ (localSectionData V').projIso.hom)
    (canonicalHom_agrees_with_twistSection :
      ∀ (V : atlas.left.left.affineOpens)
        (f : (localSectionData V).grading 1),
        HEq
          ((((Modules.pushforward π).map (canonicalHom 1)).val.app
              (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
            (chartFibreDegreeOneUnliftedSection deg π localπ localCoverHom
              (localSectionData V) f))
          (((serreTwistIso V 1).hom.val.app (op ⊤)).hom
            ((Scheme.Modules.globalSectionsPullback
                (localSectionData V).projIso.hom
                (AtlasAffineProjData.serreTwist (localSectionData V) 1)).hom
              (@Proj.AssociatedModule.twistSection (localSectionData V).A
                (localSectionData V).instCommRing
                (localSectionData V).grading (localSectionData V).instGradedAlgebra
                (n := 1) f))))
    (twistMul_agrees_with_serreMul :
      ∀ (V : atlas.left.left.affineOpens) (n m : ℕ)
        (x : (localSectionData V).grading n)
        (y : (localSectionData V).grading m),
        HEq
          (tensorSection (chartFibreOver localπ V).left.sheaf (op ⊤)
            (chartFibreTransportedTwistSection localπ localCoverHom twistModule
              localSectionData serreTwistIso V x)
            (chartFibreTransportedTwistSection localπ localCoverHom twistModule
              localSectionData serreTwistIso V y))
          (chartFibreTransportedTwistSection localπ localCoverHom twistModule
            localSectionData serreTwistIso V
            (atlasHomogeneousMul (localSectionData V).instCommRing
              (localSectionData V).grading (localSectionData V).instGradedAlgebra
              x y))) :
    Twist 𝒜 deg where
  space := space
  π := π
  twistAlgebra := twistAlgebra
  twistModule := twistModule
  twistModuleIso := twistModuleIso
  canonicalHom := canonicalHom
  canonicalHom_map_one := canonicalHom_map_one
  canonicalHom_map_mul := canonicalHom_map_mul
  atlas := atlas
  atlas_locallySurjective := atlas_locallySurjective
  localScheme := localScheme
  localπ := localπ
  localIso := localIso
  localIso_snd := localIso_snd
  localCoverHom := localCoverHom
  localCoverHom_eq := localCoverHom_eq
  localSectionData := localSectionData
  serreTwistIso := serreTwistIso
  sectionRestrict := sectionRestrict
  sectionRestrict_spec := sectionRestrict_spec
  chartRestrict := chartRestrict
  chartRestrict_over := chartRestrict_over
  projIso_restrict := projIso_restrict
  canonicalHom_agrees_with_twistSection := canonicalHom_agrees_with_twistSection
  twistMul_agrees_with_serreMul := twistMul_agrees_with_serreMul

/-- Serre's twist section of a homogeneous element of an affine chart model. -/
def chartTwistSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) {n : ℕ}
    (f : (P.localSectionData V).grading n) :
    Γ(AtlasAffineProjData.serreTwist (P.localSectionData V) n, ⊤) :=
  @Proj.AssociatedModule.twistSection (P.localSectionData V).A
    (P.localSectionData V).instCommRing
    (P.localSectionData V).grading (P.localSectionData V).instGradedAlgebra
    (n := n) f

/-- `chartTwistSection` is Serre's canonical global section of the chartwise twisting
sheaf. -/
theorem chartTwistSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) {n : ℕ}
    (f : (P.localSectionData V).grading n) :
    chartTwistSection P V f =
      @Proj.AssociatedModule.twistSection (P.localSectionData V).A
        (P.localSectionData V).instCommRing
        (P.localSectionData V).grading (P.localSectionData V).instGradedAlgebra
        (n := n) f :=
  rfl

/-- The sheaf map on the affine-chart fibre induced by `Proj.AssociatedModule.twistSection`
after `projIso` and `serreTwistIso`, as a map on global sections of the fibre restriction
of `𝒪_P(n)`. -/
def chartFibreTwistSectionOnGlobal {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) {n : ℕ}
    (f : (P.localSectionData V).grading n) :
    (chartFibreRestrictModule P.localπ P.localCoverHom V (P.twistModule n)).val.obj
      (op ⊤) :=
  ((P.serreTwistIso V n).hom.val.app (op ⊤)).hom
    ((Scheme.Modules.globalSectionsPullback
        (P.localSectionData V).projIso.hom
        (AtlasAffineProjData.serreTwist (P.localSectionData V) n)).hom
      (chartTwistSection P V f))

/-- `chartFibreTwistSectionOnGlobal` is `twistSection` transported along `projIso` and
`serreTwistIso`. -/
theorem chartFibreTwistSectionOnGlobal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) {n : ℕ}
    (f : (P.localSectionData V).grading n) :
    chartFibreTwistSectionOnGlobal P V f =
      ((P.serreTwistIso V n).hom.val.app (op ⊤)).hom
        ((Scheme.Modules.globalSectionsPullback
            (P.localSectionData V).projIso.hom
            (AtlasAffineProjData.serreTwist (P.localSectionData V) n)).hom
          (chartTwistSection P V f)) :=
  rfl

/-- Universe-unlifted degree-one section of `deg.obj 1` associated to a homogeneous
chart-model element. -/
def chartDegreeOneUnliftedSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1) :
    (deg.obj 1).val.obj
      (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens))) :=
  degreeOneUnliftedChartSection deg (P.localSectionData V) f

/-- `chartDegreeOneUnliftedSection` is the universe-down of the model section via
`deg.iso 1`. -/
theorem chartDegreeOneUnliftedSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1) :
    chartDegreeOneUnliftedSection P V f =
      degreeOneUnliftedChartSection deg (P.localSectionData V) f :=
  rfl

/-- Restriction of `π^* 𝒜_1` to the affine-chart fibre of the local relative Proj. -/
abbrev chartFibreDegreeOneModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    (chartFibreOver P.localπ V).left.Modules :=
  chartFibreRestrictModule P.localπ P.localCoverHom V
    ((Modules.pullback P.π).obj (deg.obj 1))

/-- `chartFibreDegreeOneModule` is the fibre restriction of `π^* 𝒜_1`. -/
theorem chartFibreDegreeOneModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    chartFibreDegreeOneModule P V =
      chartFibreRestrictModule P.localπ P.localCoverHom V
        ((Modules.pullback P.π).obj (deg.obj 1)) :=
  rfl

/-- Restriction of `𝒪_P(n)` to the affine-chart fibre of the local relative Proj. -/
abbrev chartFibreTwistModuleAt {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) (n : ℤ) :
    (chartFibreOver P.localπ V).left.Modules :=
  chartFibreRestrictModule P.localπ P.localCoverHom V (P.twistModule n)

/-- `chartFibreTwistModuleAt` is the fibre restriction of `𝒪_P(n)`. -/
theorem chartFibreTwistModuleAt_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) (n : ℤ) :
    chartFibreTwistModuleAt P V n =
      chartFibreRestrictModule P.localπ P.localCoverHom V (P.twistModule n) :=
  rfl

/-- Restriction of `𝒪_P(1)` to the affine-chart fibre of the local relative Proj. -/
abbrev chartFibreTwistModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    (chartFibreOver P.localπ V).left.Modules :=
  chartFibreTwistModuleAt P V 1

/-- `chartFibreTwistModule` is the fibre restriction of `𝒪_P(1)`. -/
theorem chartFibreTwistModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    chartFibreTwistModule P V = chartFibreTwistModuleAt P V 1 :=
  rfl

/-- `canonicalHom 1` pulled back to the affine-chart fibre. -/
def chartFibreCanonicalHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    chartFibreDegreeOneModule P V ⟶ chartFibreTwistModule P V :=
  (Modules.restrictToScheme (chartFibreOver P.localπ V)).map
    ((Modules.pullback (chartFibreCoverHom P.localπ P.localCoverHom V)).map
      (P.canonicalHom 1))

/-- `chartFibreCanonicalHom` is the fibre pullback of `canonicalHom 1`. -/
theorem chartFibreCanonicalHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) :
    chartFibreCanonicalHom P V =
      (Modules.restrictToScheme (chartFibreOver P.localπ V)).map
        ((Modules.pullback (chartFibreCoverHom P.localπ P.localCoverHom V)).map
          (P.canonicalHom 1)) :=
  rfl

/-- The canonical degree-one fibre section associated to a homogeneous chart-model
element. -/
def chartFibreDegreeOneSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1) :
    ((Modules.pushforward P.π).obj ((Modules.pullback P.π).obj (deg.obj 1))).val.obj
      (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens))) :=
  chartFibreDegreeOneUnliftedSection deg P.π P.localπ P.localCoverHom
    (P.localSectionData V) f

/-- `chartFibreDegreeOneSection` is the fibre transport of the unlifted chart-model
section. -/
theorem chartFibreDegreeOneSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1) :
    chartFibreDegreeOneSection P V f =
      chartFibreDegreeOneUnliftedSection deg P.π P.localπ P.localCoverHom
        (P.localSectionData V) f :=
  rfl

/-- Degree-one homogeneous chart elements as adjunction-unit sections of `π_* π^* 𝒜_1`. -/
abbrev ChartDegreeOneFibreSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :=
  ∀ (V : P.atlas.left.left.affineOpens),
    (P.localSectionData V).grading 1 →
      ((Modules.pushforward P.π).obj ((Modules.pullback P.π).obj (deg.obj 1))).val.obj
        (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)))

/-- `ChartDegreeOneFibreSection` is the type of degree-one fibre sections of `π^* 𝒜_1`. -/
theorem ChartDegreeOneFibreSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    ChartDegreeOneFibreSection P =
      ∀ (V : P.atlas.left.left.affineOpens),
        (P.localSectionData V).grading 1 →
          ((Modules.pushforward P.π).obj ((Modules.pullback P.π).obj (deg.obj 1))).val.obj
            (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens))) :=
  rfl

/-- The canonical family of degree-one fibre sections built from chart-model elements. -/
def chartDegreeOneFibreSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    ChartDegreeOneFibreSection P :=
  fun V f ↦ chartFibreDegreeOneSection P V f

/-- `chartDegreeOneFibreSection` is pointwise `chartFibreDegreeOneSection`. -/
theorem chartDegreeOneFibreSection_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1) :
    chartDegreeOneFibreSection P V f = chartFibreDegreeOneSection P V f :=
  rfl

/-- On each affine chart, `π_* canonicalHom 1` sends the transported chart-model
section to Serre's `twistSection` after `projIso` and `serreTwistIso`. -/
def CanonicalHomAgreesWithTwistSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) : Prop :=
  ∀ (V : P.atlas.left.left.affineOpens)
    (f : (P.localSectionData V).grading 1),
    HEq
      ((((Modules.pushforward P.π).map (P.canonicalHom 1)).val.app
          (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)))).hom
        (chartFibreDegreeOneSection P V f))
      (chartFibreTwistSectionOnGlobal P V f)

/-- The chartwise Serre identification of `canonicalHom 1` is the displayed comparison
of transported `twistSection` with the fibre pullback of `canonicalHom 1`. -/
theorem CanonicalHomAgreesWithTwistSection_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    CanonicalHomAgreesWithTwistSection P ↔
      ∀ (V : P.atlas.left.left.affineOpens)
        (f : (P.localSectionData V).grading 1),
        HEq
          ((((Modules.pushforward P.π).map (P.canonicalHom 1)).val.app
              (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)))).hom
            (chartFibreDegreeOneSection P V f))
          (chartFibreTwistSectionOnGlobal P V f) :=
  Iff.rfl

/-- The canonical map `π^* 𝒜_1 ⟶ 𝒪_P(1)` on the pullback side. -/
def canonicalMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    (Modules.pullback P.π).obj (deg.obj 1) ⟶ P.twistModule 1 :=
  P.canonicalHom 1

/-- `canonicalMap P` is the degree-one component of `canonicalHom`. -/
theorem canonicalMap_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    canonicalMap P = P.canonicalHom 1 :=
  rfl

/-- Universe lift of the degree-`n` twist module is the degree-`n` piece of the twist
algebra. -/
def twistModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) (n : ℤ) :
    Modules.liftModule (P.twistModule n) ≅ P.twistAlgebra n :=
  P.twistModuleIso n

/-- `twistModule_eq P n` is the stored comparison isomorphism. -/
theorem twistModule_eq_iso {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) (n : ℤ) :
    twistModule_eq P n = P.twistModuleIso n :=
  rfl

/-- Restriction of `𝒪_P(n)` to an affine chart is Serre's twisting sheaf. -/
def serreTwistIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg)
    (V : P.atlas.left.left.affineOpens) (n : ℤ) :
    (Scheme.Modules.pullback (P.localSectionData V).projIso.hom).obj
        (AtlasAffineProjData.serreTwist (P.localSectionData V) n) ≅
      chartFibreTwistModuleAt P V n :=
  P.serreTwistIso V n

/-- The étale-local covering, Serre identification, and unit conditions hold
simultaneously. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) P.atlas.hom ∧
      P.localIso.hom ≫ ofOverMap (Over.homMk P.localπ rfl) =
        etaleBaseChangeSnd P.π P.atlas ∧
      P.localCoverHom = P.localIso.inv ≫ etaleBaseChangeHom P.π P.atlas ∧
      (∀ U : smallEtaleSite P.space,
        (((Modules.liftModuleMap (P.canonicalHom 0)).val.app (op U)).hom)
            (psiSourceOneSection P.π deg (op U)) =
          ((P.twistModuleIso 0).inv.val.app (op U)).hom
            (P.twistAlgebra.one (op U))) ∧
      (∀ (V V' : P.atlas.left.left.affineOpens)
        (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens))
        (d : ℕ) (x : (P.localSectionData V').grading d),
        ((P.localSectionData V).model d
            (((𝒜 (Int.ofNat d)).val.map (atlasOpenLe P.atlas h).op).hom
              (((P.localSectionData V').model d).symm (ULift.up x)))).down =
          AtlasGradedRingHom.applied (P.localSectionData V').instCommRing
            (P.localSectionData V).instCommRing (P.sectionRestrict V V' h) x) ∧
      (∀ (V V' : P.atlas.left.left.affineOpens)
        (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens)),
        (P.localSectionData V).toAffineOpen ≫ Scheme.homOfLE P.atlas.left.left h =
          P.chartRestrict V V' h ≫ (P.localSectionData V').toAffineOpen ∧
        (P.localSectionData V).projIso.hom ≫ P.chartRestrict V V' h =
          atlasFibreRestrict P.localπ h ≫ (P.localSectionData V').projIso.hom) :=
  sorry

end Twist

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
