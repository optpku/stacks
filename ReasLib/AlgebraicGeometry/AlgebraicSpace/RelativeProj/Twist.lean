/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.RingTheory.GradedAlgebra.RingHom

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped DirectSum
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

/-! The section ring is formed before choosing any small graded-ring model. -/
namespace EtaleSectionRing

variable (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (U : smallEtaleSite X)

/-- The actual nonnegative homogeneous sections on an object of the étale site. -/
abbrev degree (n : ℕ) : Type (u + 1) := (𝒜 (Int.ofNat n)).val.obj (op U)

/-- The direct sum of the actual homogeneous sections, without any universe shrinking. -/
abbrev ring : Type (u + 1) := ⨁ n : ℕ, degree 𝒜 U n

instance instGOne : GradedMonoid.GOne (degree 𝒜 U) where
  one := 𝒜.one (op U)

instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜 U) where
  mul := fun {m n} x y ↦ 𝒜.mul (op U) (m : ℤ) (n : ℤ) x y
  mul_zero := sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry

instance instGMonoid : GradedMonoid.GMonoid (degree 𝒜 U) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry

instance instGSemiring : DirectSum.GSemiring (degree 𝒜 U) :=
  { (inferInstance : DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜 U)),
    (inferInstance : GradedMonoid.GMonoid (degree 𝒜 U)) with
    natCast := fun n ↦ n • 𝒜.one (op U)
    natCast_zero := sorry
    natCast_succ := sorry }

instance instGRing : DirectSum.GRing (degree 𝒜 U) :=
  { (inferInstance : DirectSum.GSemiring (degree 𝒜 U)) with
    intCast := fun z ↦ z • 𝒜.one (op U)
    intCast_ofNat := sorry
    intCast_negSucc_ofNat := sorry }

/-- The ring restriction is the finite-sum extension of the actual sheaf restrictions. -/
def restrict {U U' : smallEtaleSite X} (f : U ⟶ U') : ring 𝒜 U' →+* ring 𝒜 U :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (degree 𝒜 U) n).comp
      (((𝒜 (n : ℤ)).val.map f.op).hom.toAddMonoidHom)) sorry sorry

/-- Ring restriction on a homogeneous section is precisely sheaf restriction. -/
@[simp] theorem restrict_of {U U' : smallEtaleSite X} (f : U ⟶ U')
    (n : ℕ) (x : degree 𝒜 U' n) :
    restrict 𝒜 f (DirectSum.of (degree 𝒜 U') n x) =
      DirectSum.of (degree 𝒜 U) n (((𝒜 (n : ℤ)).val.map f.op).hom x) :=
  DirectSum.toSemiring_of _ _ _ _ _

end EtaleSectionRing

/-- The scalar-unit homomorphism into degree zero of an affine section model. -/
def atlasDegreeZeroStructureMap
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (U : smallEtaleSite X) {A : Type u} [CommRing A]
    (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U) ≃+ ULift.{u + 1} (grading d))
    (isModel : IsEtaleSectionModel 𝒜 U grading model) :
    Γ(U.left.left, ⊤) →+* grading 0 where
  toFun r := (model 0 (@SMul.smul ((commStructureSheafLift X).obj.obj (op U))
      ((𝒜.obj 0).val.obj (op U)) ((𝒜.obj 0).val.obj (op U)).isModule.toSMul
      (ULift.up.{u + 1} r) (𝒜.one (op U)))).down
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The structural morphism of an affine projective-spectrum model is induced by its
scalar-unit map to degree zero. -/
def atlasToAffineOpen
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (atlas : smallEtaleSite X) (V : atlas.left.left.affineOpens)
    {A : Type u} [CommRing A] (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj
        (op (openImmersionSite atlas (V : atlas.left.left.Opens))) ≃+
          ULift.{u + 1} (grading d))
    (isModel : IsEtaleSectionModel 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens)) grading model) :
    Proj grading ⟶ (V : atlas.left.left.Opens).toScheme :=
  Proj.toSpecZero grading ≫
    Spec.map (CommRingCat.ofHom (atlasDegreeZeroStructureMap 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens)) grading model isModel)) ≫
        (Scheme.isoSpec (V : atlas.left.left.Opens).toScheme).inv

/-- An explicitly supplied affine-Proj chart witness. Its geometric isomorphism is input,
not the conclusion of a relative-Proj construction. `IsEtaleSectionModel` identifies the
model with the actual section ring via `sectionRingEquiv`. No quasi-coherence is needed to
describe an individual supplied witness; the source-facing atlas witness requires it. -/
structure AtlasAffineProjWitness
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left)
    (V : atlas.left.left.affineOpens) where
  /-- A small model of the affine section ring. -/
  A : Type u
  /-- Commutative ring structure on the affine section ring. -/
  instCommRing : CommRing A
  /-- The nonnegative grading by submodules. -/
  grading : (ℕ → (@Submodule ℤ A inferInstance instCommRing.toAddCommMonoid (@AddCommGroup.toIntModule A instCommRing.toAddCommGroup)))
  /-- The grading is a graded algebra. -/
  instGradedAlgebra : @GradedAlgebra ℕ ℤ A inferInstance inferInstance inferInstance instCommRing.toSemiring (@Ring.toIntAlgebra A instCommRing.toRing) grading
  /-- Additive identification of sheaf sections with universe-lifted graded pieces. -/
  model : ∀ d : ℕ,
    (𝒜 (Int.ofNat d)).val.obj
        (op (openImmersionSite atlas (V : atlas.left.left.Opens))) ≃+
      ULift.{u + 1} (grading d)
  /-- The identification preserves the degree-zero unit and homogeneous multiplication. -/
  isModel :
    @IsEtaleSectionModel S X 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens))
      A instCommRing grading instGradedAlgebra model
  /-- The fibre of the local relative Proj over this affine open is the projective spectrum
  of the section model. -/
  projIso :
    CategoryTheory.Limits.pullback localπ (V : atlas.left.left.Opens).ι ≅
      @Proj A _ instCommRing inferInstance inferInstance grading instGradedAlgebra
  /-- The chart identification commutes with the canonical structural morphism. -/
  projIso_over :
    projIso.hom ≫
      @atlasToAffineOpen S X 𝒜 atlas V A instCommRing grading instGradedAlgebra model isModel =
        CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι

/-- Compatibility name for the explicitly supplied witness interface. This abbreviation
does not assert that such charts exist for an arbitrary scheme over the atlas. -/
abbrev AtlasAffineProjData
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left) (V : atlas.left.left.affineOpens) :=
  AtlasAffineProjWitness 𝒜 atlas localScheme localπ V

namespace AtlasAffineProjWitness

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left} {V : atlas.left.left.affineOpens}

/-- Assemble the degreewise model into a ring equivalence with the actual section ring.
Both directions are explicit finite homogeneous decompositions. -/
def sectionRingEquiv (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V) :
    letI := data.instCommRing
    EtaleSectionRing.ring 𝒜 (openImmersionSite atlas (V : atlas.left.left.Opens)) ≃+* data.A := by
  letI := data.instCommRing
  letI := data.instGradedAlgebra
  exact
    { ((DirectSum.congrAddEquiv (fun d ↦ (data.model d).trans AddEquiv.ulift)).trans
        (DirectSum.decomposeRingEquiv data.grading).symm.toAddEquiv) with
      map_mul' := sorry }

/-- The assembled ring equivalence is the given model on each homogeneous section. -/
@[simp] theorem sectionRingEquiv_of
    (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V) (d : ℕ)
    (x : EtaleSectionRing.degree 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens)) d) :
    data.sectionRingEquiv (DirectSum.of
      (EtaleSectionRing.degree 𝒜 (openImmersionSite atlas (V : atlas.left.left.Opens))) d x) =
        ((data.model d x).down : data.A) := sorry

/-- The elementary affine model supplies a genuine witness: restrict its structure map
back to the same affine open. The isomorphism uses the pullback projection and lift. -/
def ofSectionModel
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (atlas : smallEtaleSite X) (V : atlas.left.left.affineOpens)
    {A : Type u} [CommRing A] (grading : ℕ → Submodule ℤ A) [GradedAlgebra grading]
    (model : ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj
      (op (openImmersionSite atlas (V : atlas.left.left.Opens))) ≃+
        ULift.{u + 1} (grading d))
    (isModel : IsEtaleSectionModel 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens)) grading model) :
    AtlasAffineProjWitness 𝒜 atlas (Proj grading)
      (atlasToAffineOpen 𝒜 atlas V grading model isModel ≫ (V : atlas.left.left.Opens).ι) V where
  A := A
  instCommRing := inferInstance
  grading := grading
  instGradedAlgebra := inferInstance
  model := model
  isModel := isModel
  projIso :=
    { hom := pullback.fst _ _
      inv := pullback.lift (𝟙 _) (atlasToAffineOpen 𝒜 atlas V grading model isModel)
        (Category.id_comp _)
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          apply (cancel_mono (V : atlas.left.left.Opens).ι).1
          simpa only [Category.assoc] using
            (pullback.condition (f := atlasToAffineOpen 𝒜 atlas V grading model isModel ≫
              (V : atlas.left.left.Opens).ι) (g := (V : atlas.left.left.Opens).ι))
      inv_hom_id := pullback.lift_fst _ _ _ }
  projIso_over := by
    apply (cancel_mono (V : atlas.left.left.Opens).ι).1
    simpa only [Category.assoc] using
      (pullback.condition (f := atlasToAffineOpen 𝒜 atlas V grading model isModel ≫
        (V : atlas.left.left.Opens).ι) (g := (V : atlas.left.left.Opens).ι))

/-- Record the laws of a supplied witness. This is not an existence or chart theorem. -/
theorem conditions_spec
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left} {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :
    @IsEtaleSectionModel S X 𝒜
      (openImmersionSite atlas (V : atlas.left.left.Opens))
      data.A data.instCommRing data.grading data.instGradedAlgebra data.model ∧
    data.projIso.hom ≫
      @atlasToAffineOpen S X 𝒜 atlas V data.A data.instCommRing data.grading
        data.instGradedAlgebra data.model data.isModel =
      CategoryTheory.Limits.pullback.snd localπ (V : atlas.left.left.Opens).ι :=
  ⟨data.isModel, data.projIso_over⟩

/-- Serre's twisting sheaf of index `n` on the affine projective spectrum of this chart. -/
def serreTwist {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) (n : ℤ) :
    (@Proj data.A _ data.instCommRing inferInstance inferInstance data.grading data.instGradedAlgebra).Modules :=
  @Proj.AssociatedModule.twistingSheaf ℤ data.A inferInstance data.instCommRing
      (@Ring.toIntAlgebra data.A data.instCommRing.toRing) data.grading data.instGradedAlgebra n

end AtlasAffineProjWitness

namespace AtlasAffineProjData

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left} {V : atlas.left.left.affineOpens}

abbrev A (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.A data
abbrev instCommRing (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.instCommRing data
abbrev grading (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.grading data
abbrev instGradedAlgebra (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.instGradedAlgebra data
abbrev model (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.model data
abbrev isModel (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.isModel data
abbrev projIso (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.projIso data
abbrev projIso_over (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V) :=
  AtlasAffineProjWitness.projIso_over data

export AtlasAffineProjWitness
  (mk ofSectionModel sectionRingEquiv serreTwist conditions_spec)

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

namespace AtlasAffineProjWitness

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left} {V V' : atlas.left.left.affineOpens}

/-- The graded model restriction is transported from the actual section-ring restriction,
using the assembled ring equivalences. It is not additional witness data. -/
def sectionRestrict (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V)
    (data' : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V')
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)) :
    @GradedRingHom ℕ data'.A data.A _ _ data'.instCommRing.toSemiring
      data.instCommRing.toSemiring inferInstance inferInstance data'.grading data.grading := by
  letI := data.instCommRing
  letI := data'.instCommRing
  exact
    { toRingHom := (data.sectionRingEquiv.toRingHom.comp
        (EtaleSectionRing.restrict 𝒜 (atlasOpenLe atlas h))).comp
          data'.sectionRingEquiv.symm.toRingHom
      map_mem := sorry }

/-- The model restriction agrees with sheaf restriction in every nonnegative degree. -/
theorem sectionRestrict_spec (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V)
    (data' : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V')
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens))
    (d : ℕ) (x : data'.grading d) :
    letI := data.instCommRing
    letI := data'.instCommRing
    ((data.model d (((𝒜 (Int.ofNat d)).val.map (atlasOpenLe atlas h).op).hom
      ((data'.model d).symm (ULift.up x)))).down : data.A) =
        (sectionRestrict data data' h).toRingHom x := sorry

/-- Quasi-coherence identifies restriction with scalar extension (Stacks 01NO), so its
projective domain is all of the smaller chart. -/
theorem sectionRestrict_domain (hqc : 𝒜.IsQuasicoherent)
    (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V)
    (data' : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V')
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)) :
    letI := data.instCommRing
    letI := data'.instCommRing
    letI := data.instGradedAlgebra
    letI := data'.instGradedAlgebra
    projMapDomain (sectionRestrict data data' h) = ⊤ := sorry

/-- The actual Proj map of the section restriction, extended from its full natural domain.
Only the proof that the domain is full uses quasi-coherence. -/
def chartRestrict (hqc : 𝒜.IsQuasicoherent)
    (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V)
    (data' : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V')
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)) :
    @Proj data.A _ data.instCommRing inferInstance inferInstance data.grading data.instGradedAlgebra ⟶
      @Proj data'.A _ data'.instCommRing inferInstance inferInstance data'.grading data'.instGradedAlgebra := by
  letI := data.instCommRing
  letI := data'.instCommRing
  letI := data.instGradedAlgebra
  letI := data'.instGradedAlgebra
  exact Proj.AssociatedModule.GradedMap.fullMap.{u, 0, 0}
    (sectionRestrict data data' h) (sectionRestrict_domain hqc data data' h)

/-- The restriction-induced chart map lies over inclusion of the affine base opens. -/
theorem chartRestrict_over (hqc : 𝒜.IsQuasicoherent)
    (data : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V)
    (data' : AtlasAffineProjWitness 𝒜 atlas localScheme localπ V')
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)) :
    @atlasToAffineOpen S X 𝒜 atlas V data.A data.instCommRing data.grading
        data.instGradedAlgebra data.model data.isModel ≫ Scheme.homOfLE atlas.left.left h =
      chartRestrict hqc data data' h ≫
        @atlasToAffineOpen S X 𝒜 atlas V' data'.A data'.instCommRing data'.grading
          data'.instGradedAlgebra data'.model data'.isModel := sorry

/-- Compatibility of supplied geometric identifications with the actual restriction maps
(Stacks 01NQ). This property belongs to the chart family, independently of twists. -/
def IsCoherent (hqc : 𝒜.IsQuasicoherent)
    (chart : ∀ V, AtlasAffineProjWitness 𝒜 atlas localScheme localπ V) : Prop :=
  ∀ (V V' : atlas.left.left.affineOpens)
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens)),
    (chart V).projIso.hom ≫ chartRestrict hqc (chart V) (chart V') h =
      atlasFibreRestrict localπ h ≫ (chart V').projIso.hom

end AtlasAffineProjWitness

/-- An explicitly supplied coherent family of affine-Proj chart witnesses for a
quasi-coherent algebra. This records the output of gluing; it does not construct it. -/
structure AtlasAffineProjAtlasWitness
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (hqc : 𝒜.IsQuasicoherent) (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left) where
  /-- The supplied affine chart identifications. -/
  chart : ∀ V, AtlasAffineProjWitness 𝒜 atlas localScheme localπ V
  /-- The identifications commute with the restriction-induced Proj maps. -/
  coherent : AtlasAffineProjWitness.IsCoherent hqc chart

namespace AtlasAffineProjAtlasWitness

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {hqc : 𝒜.IsQuasicoherent} {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}

/-- Triple-open compatibility is a property of the chart family (Stacks 01NP). -/
theorem chartRestrict_comp (data : AtlasAffineProjAtlasWitness 𝒜 hqc atlas localScheme localπ)
    (V V' V'' : atlas.left.left.affineOpens)
    (h : (V : atlas.left.left.Opens) ≤ (V' : atlas.left.left.Opens))
    (h' : (V' : atlas.left.left.Opens) ≤ (V'' : atlas.left.left.Opens)) :
    AtlasAffineProjWitness.chartRestrict hqc (data.chart V) (data.chart V') h ≫
      AtlasAffineProjWitness.chartRestrict hqc (data.chart V') (data.chart V'') h' =
        AtlasAffineProjWitness.chartRestrict hqc (data.chart V) (data.chart V'') (h.trans h') := sorry

end AtlasAffineProjAtlasWitness

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
    [Etale localCoverHom]
    (V : atlas.left.left.affineOpens) :
    Etale (chartFibreCoverHom localπ localCoverHom V) :=
  sorry

/-- The affine-chart fibre as an object of the small étale site of the twist space. -/
def chartFibreSite {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    [Etale localCoverHom]
    (V : atlas.left.left.affineOpens) : smallEtaleSite space :=
  smallEtaleSite.mk (chartFibreCoverHom localπ localCoverHom V)

/-- `chartFibreSite` is `smallEtaleSite.mk` of the fibre covering morphism. -/
theorem chartFibreSite_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    [Etale localCoverHom]
    (V : atlas.left.left.affineOpens) :
    chartFibreSite localπ localCoverHom V =
      smallEtaleSite.mk (chartFibreCoverHom localπ localCoverHom V) :=
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


/-- Étaleness of a local cover follows from its base-change realization. -/
private theorem localCoverEtale {space : AlgebraicSpace S} (π : space ⟶ X)
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left)
    (e : etaleBaseChangeSpace π atlas ≅ ofOver (localCoverOver atlas localScheme localπ))
    (h : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (he : h = e.inv ≫ etaleBaseChangeHom π atlas) : Etale h := by
  rw [he]
  infer_instance


set_option backward.privateInPublic true in
/-- The projection of an affine-chart fibre to its affine base open, over the ground scheme. -/
@[expose] private def fibreBaseHom {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left) (V : atlas.left.left.affineOpens) :
    chartFibreOver localπ V ⟶ openImmersionOver atlas (V : atlas.left.left.Opens) :=
  Over.homMk (pullback.snd localπ (V : atlas.left.left.Opens).ι) (by
    change pullback.snd localπ (V : atlas.left.left.Opens).ι ≫
        ((V : atlas.left.left.Opens).ι ≫ atlas.left.hom) =
      pullback.fst localπ (V : atlas.left.left.Opens).ι ≫ localπ ≫ atlas.left.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ atlas.left.hom)
        (pullback.condition (f := localπ) (g := (V : atlas.left.left.Opens).ι)).symm).trans
          (Category.assoc _ _ _)))

/-- The fibre inclusion and base projection commute with the local structure morphism. -/
private theorem fibreBaseHom_comm {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left) (V : atlas.left.left.affineOpens) :
    chartFibreOverHom localπ V ≫ (Over.homMk localπ rfl :
      localCoverOver atlas localScheme localπ ⟶ atlas.left) =
      fibreBaseHom localπ V ≫ openImmersionMap atlas (V : atlas.left.left.Opens) := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- A locally realized cover has the expected morphism to the base algebraic space. -/
private theorem fibreCover_over {space : AlgebraicSpace S} (π : space ⟶ X)
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left)
    (e : etaleBaseChangeSpace π atlas ≅ ofOver (localCoverOver atlas localScheme localπ))
    (he : e.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas)
    (h : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (hh : h = e.inv ≫ etaleBaseChangeHom π atlas) (V : atlas.left.left.affineOpens) :
    chartFibreCoverHom localπ h V ≫ π =
      ofOverMap (fibreBaseHom localπ V) ≫ (openImmersionSite atlas (V : atlas.left.left.Opens)).hom := by
  have hc : etaleBaseChangeHom π atlas ≫ π = etaleBaseChangeSnd π atlas ≫ atlas.hom :=
    (show pullback.fst (homFunctor π) (homFunctor atlas.hom) ≫ homFunctor π =
      pullback.snd (homFunctor π) (homFunctor atlas.hom) ≫ homFunctor atlas.hom from
        pullback.condition)
  have hlocal : h ≫ π = ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom := by
    calc
      h ≫ π = (e.inv ≫ etaleBaseChangeHom π atlas) ≫ π := congrArg (fun k ↦ k ≫ π) hh
      _ = e.inv ≫ (etaleBaseChangeHom π atlas ≫ π) := Category.assoc _ _ _
      _ = e.inv ≫ (etaleBaseChangeSnd π atlas ≫ atlas.hom) := congrArg (fun k ↦ e.inv ≫ k) hc
      _ = e.inv ≫ ((e.hom ≫ ofOverMap (Over.homMk localπ rfl)) ≫ atlas.hom) :=
        congrArg (fun k ↦ e.inv ≫ (k ≫ atlas.hom)) he.symm
      _ = ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom := by
        simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hmap : ofOverMap (chartFibreOverHom localπ V) ≫ ofOverMap (Over.homMk localπ rfl) =
      ofOverMap (fibreBaseHom localπ V) ≫ ofOverMap (openImmersionMap atlas (V : atlas.left.left.Opens)) :=
    ((ofOverFunctor S).map_comp _ _).symm.trans
      ((congrArg (ofOverFunctor S).map (fibreBaseHom_comm localπ V)).trans
        ((ofOverFunctor S).map_comp _ _))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ ofOverMap (chartFibreOverHom localπ V) ≫ k) hlocal).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ atlas.hom) hmap).trans (Category.assoc _ _ _))))

set_option backward.privateInPublic true in
/-- The actual fibre chart gives a structured arrow into the base-change chart. -/
@[expose] private def fibreEvaluationChart {space : AlgebraicSpace S} (π : space ⟶ X)
    (atlas : smallEtaleSite X) (localScheme : Scheme.{u})
    (localπ : localScheme ⟶ atlas.left.left)
    (e : etaleBaseChangeSpace π atlas ≅ ofOver (localCoverOver atlas localScheme localπ))
    (he : e.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas)
    (h : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    (hh : h = e.inv ≫ etaleBaseChangeHom π atlas)
    (V : atlas.left.left.affineOpens) :
    let hf := localCoverEtale π atlas localScheme localπ e h hh
    let f := chartFibreCoverHom localπ h V
    let U := @Modules.restrictPostcompose S _ _ f
      (@etale_chartFibreCoverHom S X atlas localScheme localπ space h hf V) |>.obj
        (Modules.RestrictToScheme.siteObject (chartFibreOver localπ V) ⊤)
    StructuredArrow (op ((etaleBaseChange π).obj
      (openImmersionSite atlas (V : atlas.left.left.Opens)))) ((smallEtaleToSpaces space).op)
      := by
  let hf := localCoverEtale π atlas localScheme localπ e h hh
  let f := chartFibreCoverHom localπ h V
  let hf' := @etale_chartFibreCoverHom S X atlas localScheme localπ space h hf V
  let W := Modules.RestrictToScheme.siteObject (chartFibreOver localπ V) ⊤
  let U := (@Modules.restrictPostcompose S _ _ f hf').obj W
  let b := W.hom ≫ ofOverMap (fibreBaseHom localπ V)
  have hw : U.hom ≫ π = b ≫ (openImmersionSite atlas (V : atlas.left.left.Opens)).hom := by
    change (W.hom ≫ f) ≫ π = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ W.hom ≫ k)
        (fibreCover_over π atlas localScheme localπ e he h hh V)).trans
          (Category.assoc _ _ _).symm)
  let q : (smallEtaleToSpaces space).obj U ⟶
      (etaleBaseChange π).obj (openImmersionSite atlas (V : atlas.left.left.Opens)) :=
    MorphismProperty.Over.homMk
      (pullback.lift (homFunctor U.hom) (homFunctor b) hw) (by
        exact pullback.lift_fst (homFunctor U.hom) (homFunctor b) hw)
  exact StructuredArrow.mk q.op

set_option backward.privateInPublic true in
/-- Étale restriction and scheme restriction give concrete sections at an open chart. -/
@[expose] private def fibreSectionToEtale {Z : Over S} {Y : AlgebraicSpace S}
    (f : ofOver Z ⟶ Y) [Etale f] (M : Y.Modules) (W : Z.left.Opens)
    (s : ((Modules.restrictToScheme Z).obj ((Modules.pullback f).obj M)).val.obj (op W)) :
    M.val.obj (op ((Modules.restrictPostcompose f).obj
      (Modules.RestrictToScheme.siteObject Z W))) :=
  (((Modules.restrictIsoPullback M f).inv.val.app
      (op (Modules.RestrictToScheme.siteObject Z W))).hom)
    (Modules.RestrictToScheme.sectionEquiv Z ((Modules.pullback f).obj M) W s)

set_option backward.privateInPublic true in
/-- A section on the postcomposed open chart determines the corresponding fibre section. -/
@[expose] private def fibreSectionFromEtale {Z : Over S} {Y : AlgebraicSpace S}
    (f : ofOver Z ⟶ Y) [Etale f] (M : Y.Modules) (W : Z.left.Opens)
    (s : M.val.obj (op ((Modules.restrictPostcompose f).obj
      (Modules.RestrictToScheme.siteObject Z W)))) :
    ((Modules.restrictToScheme Z).obj ((Modules.pullback f).obj M)).val.obj (op W) :=
  (Modules.RestrictToScheme.sectionEquiv Z ((Modules.pullback f).obj M) W).symm
    ((((Modules.restrictIsoPullback M f).hom.val.app
      (op (Modules.RestrictToScheme.siteObject Z W))).hom) s)

set_option backward.privateInPublic true in
/-- Multiplication of integral twist sections on any open of an affine-chart fibre,
using the actual graded algebra multiplication and the restriction comparisons. -/
def chartFibreAlgebraMul {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left) {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    [Etale localCoverHom]
    (twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space))
    (twistModule : ℤ → space.Modules)
    (twistModuleIso : ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n)
    (V : atlas.left.left.affineOpens) (W : (chartFibreOver localπ V).left.Opens)
    (n m : ℤ)
    (s : (chartFibreRestrictModule localπ localCoverHom V (twistModule n)).val.obj (op W))
    (t : (chartFibreRestrictModule localπ localCoverHom V (twistModule m)).val.obj (op W)) :
    (chartFibreRestrictModule localπ localCoverHom V (twistModule (n + m))).val.obj (op W) :=
  let f := chartFibreCoverHom localπ localCoverHom V
  let U := op ((Modules.restrictPostcompose f).obj
    (Modules.RestrictToScheme.siteObject (chartFibreOver localπ V) W))
  let toLift := fun (k : ℤ) (x : (twistModule k).val.obj U) ↦
    ofLiftedSection (twistModule k) U
      (upLiftedCommSection ((Modules.toCommModules space).obj (twistModule k)) U
        (asCommSection (twistModule k) x))
  let a := ((twistModuleIso n).hom.val.app U).hom
    (toLift n (fibreSectionToEtale f (twistModule n) W s))
  let b := ((twistModuleIso m).hom.val.app U).hom
    (toLift m (fibreSectionToEtale f (twistModule m) W t))
  let result := ((twistModuleIso (n + m)).inv.val.app U).hom
    (twistAlgebra.mul U n m a b)
  fibreSectionFromEtale f (twistModule (n + m)) W
    (ofCommSection (twistModule (n + m))
      (asLiftedSection (twistModule (n + m)) U result).down)

set_option backward.privateInPublic true in
/-- The displayed fibre multiplication is defined by the actual graded multiplication. -/
theorem chartFibreAlgebraMul_eq {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left) {space : AlgebraicSpace S}
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    [Etale localCoverHom]
    (twistAlgebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift space))
    (twistModule : ℤ → space.Modules)
    (twistModuleIso : ∀ n : ℤ, Modules.liftModule (twistModule n) ≅ twistAlgebra n)
    (V : atlas.left.left.affineOpens) (W : (chartFibreOver localπ V).left.Opens)
    (n m : ℤ)
    (s : (chartFibreRestrictModule localπ localCoverHom V (twistModule n)).val.obj (op W))
    (t : (chartFibreRestrictModule localπ localCoverHom V (twistModule m)).val.obj (op W)) :
    chartFibreAlgebraMul localπ localCoverHom twistAlgebra twistModule twistModuleIso V W n m s t =
      (let f := chartFibreCoverHom localπ localCoverHom V
       let U := op ((Modules.restrictPostcompose f).obj
         (Modules.RestrictToScheme.siteObject (chartFibreOver localπ V) W))
       let toLift := fun (k : ℤ) (x : (twistModule k).val.obj U) ↦
         ofLiftedSection (twistModule k) U
           (upLiftedCommSection ((Modules.toCommModules space).obj (twistModule k)) U
             (asCommSection (twistModule k) x))
       let a := ((twistModuleIso n).hom.val.app U).hom
         (toLift n (fibreSectionToEtale f (twistModule n) W s))
       let b := ((twistModuleIso m).hom.val.app U).hom
         (toLift m (fibreSectionToEtale f (twistModule m) W t))
       let result := ((twistModuleIso (n + m)).inv.val.app U).hom
         (twistAlgebra.mul U n m a b)
       fibreSectionFromEtale f (twistModule (n + m)) W
         (ofCommSection (twistModule (n + m))
           (asLiftedSection (twistModule (n + m)) U result).down)) := rfl

set_option backward.privateInPublic true in
/-- An explicitly supplied twist presentation for a quasi-coherent graded algebra sheaf.
The local affine-Proj identifications and their coherence are witnesses, not an existence
theorem or a construction of relative Proj by gluing. -/
structure Twist {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) where
  /-- The source algebra satisfies the quasi-coherence hypothesis of Stacks 01NN. -/
  algebra_isQuasicoherent : 𝒜.IsQuasicoherent
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
  /-- A scheme étale over `X` giving a surjective atlas. -/
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
  /-- Supplied coherent affine-Proj witnesses, independently of the twist modules. -/
  localCharts : AtlasAffineProjAtlasWitness 𝒜 algebra_isQuasicoherent atlas localScheme localπ
  /-- Restriction of `𝒪_P(n)` to each affine chart recovers Serre's twisting sheaf. -/
  serreTwistIso :
    ∀ (V : atlas.left.left.affineOpens) (n : ℤ),
      (Scheme.Modules.pullback (localCharts.chart V).projIso.hom).obj
          (AtlasAffineProjData.serreTwist (localCharts.chart V) n) ≅
        chartFibreRestrictModule localπ localCoverHom V (twistModule n)
  /-- On each affine chart the actual evaluation of the pushed-forward degree-one map
  is Serre's canonical homogeneous section. -/
  canonicalHom_agrees_with_twistSection :
    ∀ (V : atlas.left.left.affineOpens) (f : (localCharts.chart V).grading 1),
      let hf : Etale localCoverHom := by
        rw [localCoverHom_eq]
        infer_instance
      let cover := chartFibreCoverHom localπ localCoverHom V
      let hf' := @etale_chartFibreCoverHom S X atlas localScheme localπ space localCoverHom hf V
      let c := fibreEvaluationChart π atlas localScheme localπ localIso localIso_snd
        localCoverHom localCoverHom_eq V
      ofUnderlyingSection (twistModule 1)
        (moduleChartValue π (twistModule 1)
          (openImmersionSite atlas (V : atlas.left.left.Opens)) c
          ((((Modules.pushforward π).map (canonicalHom 1)).val.app
            (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
              (chartFibreDegreeOneUnliftedSection deg π localπ localCoverHom
                (localCharts.chart V) f))) =
        @fibreSectionToEtale S (chartFibreOver localπ V) space cover hf' (twistModule 1) ⊤
          (chartFibreTransportedTwistSection localπ localCoverHom twistModule
            localCharts.chart serreTwistIso V f)
  /-- The actual graded multiplication is canonical Serre multiplication in every pair
  of integral degrees and over every open of each projective chart. -/
  twistMul_agrees_with_serreMul :
    ∀ (V : atlas.left.left.affineOpens) (n m : ℤ)
      (W : (@Proj (localCharts.chart V).A _ (localCharts.chart V).instCommRing
        inferInstance inferInstance (localCharts.chart V).grading
          (localCharts.chart V).instGradedAlgebra).Opens)
      (s : (AtlasAffineProjData.serreTwist (localCharts.chart V) n).val.obj (op W))
      (t : (AtlasAffineProjData.serreTwist (localCharts.chart V) m).val.obj (op W)),
      let hf : Etale localCoverHom := by
        rw [localCoverHom_eq]
        infer_instance
      let W' := (localCharts.chart V).projIso.hom ⁻¹ᵁ W
      let transport := fun (k : ℤ)
          (x : (AtlasAffineProjData.serreTwist (localCharts.chart V) k).val.obj (op W)) ↦
        ((serreTwistIso V k).hom.val.app (op W')).hom
          ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction (localCharts.chart V).projIso.hom).unit.app
              (AtlasAffineProjData.serreTwist (localCharts.chart V) k)) W).hom x)
      @chartFibreAlgebraMul S X atlas localScheme localπ space localCoverHom hf
        twistAlgebra twistModule twistModuleIso V W' n m (transport n s) (transport m t) =
      transport (n + m)
        (@Proj.AssociatedModule.CanonicalAlgebra.mulSection ℤ (localCharts.chart V).A
          inferInstance (localCharts.chart V).instCommRing
          (@Ring.toIntAlgebra (localCharts.chart V).A (localCharts.chart V).instCommRing.toRing)
          (localCharts.chart V).grading (localCharts.chart V).instGradedAlgebra (op W) n m s t)

namespace Twist

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜}

/-- Compatibility projection of the supplied affine charts from their coherent owner. -/
abbrev localSectionData (P : Twist 𝒜 deg) := P.localCharts.chart

/-- The old restriction API now computes from actual sheaf restriction. -/
def sectionRestrict (P : Twist 𝒜 deg) (V V' : P.atlas.left.left.affineOpens)
    (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens)) :=
  AtlasAffineProjWitness.sectionRestrict (P.localSectionData V) (P.localSectionData V') h

/-- Model restriction agrees with the given layer of the algebra sheaf. -/
theorem sectionRestrict_spec (P : Twist 𝒜 deg) (V V' : P.atlas.left.left.affineOpens)
    (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens))
    (d : ℕ) (x : (P.localSectionData V').grading d) :
    letI := (P.localSectionData V).instCommRing
    letI := (P.localSectionData V').instCommRing
    (((P.localSectionData V).model d
      (((𝒜 (Int.ofNat d)).val.map (atlasOpenLe P.atlas h).op).hom
        (((P.localSectionData V').model d).symm (ULift.up x)))).down :
          (P.localSectionData V).A) = (P.sectionRestrict V V' h).toRingHom x :=
  AtlasAffineProjWitness.sectionRestrict_spec (P.localSectionData V) (P.localSectionData V') h d x

/-- The old chart restriction API is the actual Proj map of the section restriction. -/
def chartRestrict (P : Twist 𝒜 deg) (V V' : P.atlas.left.left.affineOpens)
    (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens)) :=
  AtlasAffineProjWitness.chartRestrict P.algebra_isQuasicoherent
    (P.localSectionData V) (P.localSectionData V') h

/-- The actual chart restriction commutes with the affine base maps. -/
theorem chartRestrict_over (P : Twist 𝒜 deg) (V V' : P.atlas.left.left.affineOpens)
    (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens)) :
    @atlasToAffineOpen S X 𝒜 P.atlas V (P.localSectionData V).A
        (P.localSectionData V).instCommRing (P.localSectionData V).grading
        (P.localSectionData V).instGradedAlgebra (P.localSectionData V).model
        (P.localSectionData V).isModel ≫ Scheme.homOfLE P.atlas.left.left h =
      P.chartRestrict V V' h ≫
        @atlasToAffineOpen S X 𝒜 P.atlas V' (P.localSectionData V').A
          (P.localSectionData V').instCommRing (P.localSectionData V').grading
          (P.localSectionData V').instGradedAlgebra (P.localSectionData V').model
          (P.localSectionData V').isModel :=
  AtlasAffineProjWitness.chartRestrict_over P.algebra_isQuasicoherent
    (P.localSectionData V) (P.localSectionData V') h

/-- Nested-open coherence is supplied by the chart owner, independently of twists. -/
theorem projIso_restrict (P : Twist 𝒜 deg) (V V' : P.atlas.left.left.affineOpens)
    (h : (V : P.atlas.left.left.Opens) ≤ (V' : P.atlas.left.left.Opens)) :
    (P.localSectionData V).projIso.hom ≫ P.chartRestrict V V' h =
      atlasFibreRestrict P.localπ h ≫ (P.localSectionData V').projIso.hom :=
  P.localCharts.coherent V V' h

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

set_option backward.privateInPublic true in
/-- The canonical degree-one map is the Serre homogeneous-section map on every affine chart. -/
def CanonicalHomAgreesWithTwistSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) : Prop :=
    ∀ (V : P.atlas.left.left.affineOpens) (f : (P.localSectionData V).grading 1),
      let hf : Etale P.localCoverHom := by
        rw [P.localCoverHom_eq]
        infer_instance
      let cover := chartFibreCoverHom P.localπ P.localCoverHom V
      let hf' := @etale_chartFibreCoverHom S X P.atlas P.localScheme P.localπ P.space P.localCoverHom hf V
      let c := fibreEvaluationChart P.π P.atlas P.localScheme P.localπ P.localIso P.localIso_snd
        P.localCoverHom P.localCoverHom_eq V
      ofUnderlyingSection (P.twistModule 1)
        (moduleChartValue P.π (P.twistModule 1)
          (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)) c
          ((((Modules.pushforward P.π).map (P.canonicalHom 1)).val.app
            (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)))).hom
              (chartFibreDegreeOneUnliftedSection deg P.π P.localπ P.localCoverHom
                (P.localSectionData V) f))) =
        @fibreSectionToEtale S (chartFibreOver P.localπ V) P.space cover hf' (P.twistModule 1) ⊤
          (chartFibreTransportedTwistSection P.localπ P.localCoverHom P.twistModule
            P.localSectionData P.serreTwistIso V f)

set_option backward.privateInPublic true in
/-- The canonical-section condition compares evaluated sections in the same module. -/
theorem CanonicalHomAgreesWithTwistSection_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    CanonicalHomAgreesWithTwistSection P ↔
    ∀ (V : P.atlas.left.left.affineOpens) (f : (P.localSectionData V).grading 1),
      let hf : Etale P.localCoverHom := by
        rw [P.localCoverHom_eq]
        infer_instance
      let cover := chartFibreCoverHom P.localπ P.localCoverHom V
      let hf' := @etale_chartFibreCoverHom S X P.atlas P.localScheme P.localπ P.space P.localCoverHom hf V
      let c := fibreEvaluationChart P.π P.atlas P.localScheme P.localπ P.localIso P.localIso_snd
        P.localCoverHom P.localCoverHom_eq V
      ofUnderlyingSection (P.twistModule 1)
        (moduleChartValue P.π (P.twistModule 1)
          (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)) c
          ((((Modules.pushforward P.π).map (P.canonicalHom 1)).val.app
            (op (openImmersionSite P.atlas (V : P.atlas.left.left.Opens)))).hom
              (chartFibreDegreeOneUnliftedSection deg P.π P.localπ P.localCoverHom
                (P.localSectionData V) f))) =
        @fibreSectionToEtale S (chartFibreOver P.localπ V) P.space cover hf' (P.twistModule 1) ⊤
          (chartFibreTransportedTwistSection P.localπ P.localCoverHom P.twistModule
            P.localSectionData P.serreTwistIso V f) := Iff.rfl

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

set_option backward.privateInPublic true in
/-- The atlas realization, canonical degree-one section comparison, and integral
multiplication comparison hold simultaneously. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (P : Twist 𝒜 deg) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) P.atlas.hom ∧
    P.localIso.hom ≫ ofOverMap (Over.homMk P.localπ rfl) =
      etaleBaseChangeSnd P.π P.atlas ∧
    P.localCoverHom = P.localIso.inv ≫ etaleBaseChangeHom P.π P.atlas ∧
    (∀ V : P.atlas.left.left.affineOpens,
      (P.localSectionData V).projIso.hom ≫
        @atlasToAffineOpen S X 𝒜 P.atlas V (P.localSectionData V).A
          (P.localSectionData V).instCommRing (P.localSectionData V).grading
          (P.localSectionData V).instGradedAlgebra (P.localSectionData V).model
          (P.localSectionData V).isModel =
        pullback.snd P.localπ (V : P.atlas.left.left.Opens).ι) ∧
    CanonicalHomAgreesWithTwistSection P ∧
    (    ∀ (V : P.atlas.left.left.affineOpens) (n m : ℤ)
      (W : (@Proj (P.localSectionData V).A _ (P.localSectionData V).instCommRing
        inferInstance inferInstance (P.localSectionData V).grading
          (P.localSectionData V).instGradedAlgebra).Opens)
      (s : (AtlasAffineProjData.serreTwist (P.localSectionData V) n).val.obj (op W))
      (t : (AtlasAffineProjData.serreTwist (P.localSectionData V) m).val.obj (op W)),
      let hf : Etale P.localCoverHom := by
        rw [P.localCoverHom_eq]
        infer_instance
      let W' := (P.localSectionData V).projIso.hom ⁻¹ᵁ W
      let transport := fun (k : ℤ)
          (x : (AtlasAffineProjData.serreTwist (P.localSectionData V) k).val.obj (op W)) ↦
        ((P.serreTwistIso V k).hom.val.app (op W')).hom
          ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction (P.localSectionData V).projIso.hom).unit.app
              (AtlasAffineProjData.serreTwist (P.localSectionData V) k)) W).hom x)
      @chartFibreAlgebraMul S X P.atlas P.localScheme P.localπ P.space P.localCoverHom hf
        P.twistAlgebra P.twistModule P.twistModuleIso V W' n m (transport n s) (transport m t) =
      transport (n + m)
        (@Proj.AssociatedModule.CanonicalAlgebra.mulSection ℤ (P.localSectionData V).A
          inferInstance (P.localSectionData V).instCommRing
          (@Ring.toIntAlgebra (P.localSectionData V).A (P.localSectionData V).instCommRing.toRing)
          (P.localSectionData V).grading (P.localSectionData V).instGradedAlgebra (op W) n m s t)) := sorry

end Twist

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
