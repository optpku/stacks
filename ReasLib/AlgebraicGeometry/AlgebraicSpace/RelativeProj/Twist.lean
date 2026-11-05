/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.SchemeComparison
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

/-- Homogeneous elements of an affine chart model in any nonnegative degree, as
universe-unlifted sections of `deg.obj n` on the corresponding étale open. -/
def degreeUnliftedChartSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    {n : ℕ} (f : data.grading n) :
    (deg.obj n).val.obj
      (op (openImmersionSite atlas (V : atlas.left.left.Opens))) :=
  (((deg.iso n).inv.val.app
      (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
    ((data.model n).symm (ULift.up f))).down

/-- `degreeUnliftedChartSection` is the universe-down of the inverse chart model. -/
theorem degreeUnliftedChartSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    {localπ : localScheme ⟶ atlas.left.left}
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    {n : ℕ} (f : data.grading n) :
    degreeUnliftedChartSection deg data f =
      (((deg.iso n).inv.val.app
          (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
        ((data.model n).symm (ULift.up f))).down :=
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
  degreeUnliftedChartSection deg data f

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

/-- Transport of a homogeneous chart-model section along the chart fibre of `π`, as the
adjunction-unit section of `π_* π^* 𝒜_n` on the affine chart open. -/
def chartFibreDegreeUnliftedSection {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {space : AlgebraicSpace S} (π : space ⟶ X)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    {n : ℕ} (f : data.grading n) :
    ((Modules.pushforward π).obj ((Modules.pullback π).obj (deg.obj n))).val.obj
      (op (openImmersionSite atlas (V : atlas.left.left.Opens))) :=
  (((Modules.pullbackPushforwardAdjunction π).unit.app (deg.obj n)).val.app
      (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
    (degreeUnliftedChartSection deg data f)

/-- `chartFibreDegreeUnliftedSection` is the adjunction-unit image of the unlifted
chart-model section. -/
theorem chartFibreDegreeUnliftedSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜)
    {space : AlgebraicSpace S} (π : space ⟶ X)
    {atlas : smallEtaleSite X} {localScheme : Scheme.{u}}
    (localπ : localScheme ⟶ atlas.left.left)
    (localCoverHom : ofOver (localCoverOver atlas localScheme localπ) ⟶ space)
    {V : atlas.left.left.affineOpens}
    (data : AtlasAffineProjData 𝒜 atlas localScheme localπ V)
    {n : ℕ} (f : data.grading n) :
    chartFibreDegreeUnliftedSection deg π localπ localCoverHom data f =
      (((Modules.pullbackPushforwardAdjunction π).unit.app (deg.obj n)).val.app
          (op (openImmersionSite atlas (V : atlas.left.left.Opens)))).hom
        (degreeUnliftedChartSection deg data f) :=
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
  chartFibreDegreeUnliftedSection deg π localπ localCoverHom data f

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
/-- The relative Proj of a quasi-coherent commutative graded `𝒪_X`-algebra, anchored to the
quadruple functor. The space, projection, Serre twists, and universal map are the canonical
objects `toAlgebraicSpace`, `CanonicalTwists.algebra` / `obj` / `psi`; they are not supplied
by the caller. Stacks 084C, 084D, 01NR, and 01O0.

The referenced descent constructions still carry proof debts; this wrapper does not
discharge their existing proof obligations. -/
structure Twist {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) : Type (u + 2) where
  /-- The relative Proj functor. Its fields record quasi-coherence and ordinary commutativity
  of `𝒜`. -/
  functor : ProjFunctor X 𝒜
  /-- `functor` classifies equivalence classes of relative projective quadruples. -/
  associated : functor.IsAssociatedToQuadruples deg

namespace Twist

variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜}

/-- Package a quadruple functor as the relative Proj it represents. -/
def ofFunctor (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg) :
    Twist 𝒜 deg where
  functor := F
  associated := hF

/-- `ofFunctor` stores the given functor. -/
theorem ofFunctor_functor (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg) :
    (ofFunctor F hF).functor = F :=
  rfl

/-- `ofFunctor` stores the given quadruple association. -/
theorem ofFunctor_associated (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg) :
    (ofFunctor F hF).associated = hF :=
  rfl

/-- The source algebra of a relative Proj is quasi-coherent. -/
theorem algebra_isQuasicoherent (P : Twist 𝒜 deg) : 𝒜.IsQuasicoherent :=
  P.functor.algebra_isQuasicoherent

/-- The source algebra of a relative Proj is ordinarily commutative. -/
theorem algebra_isCommutative (P : Twist 𝒜 deg) : 𝒜.IsCommutative :=
  P.functor.algebra_isCommutative

/-- The algebraic space `P = underline{Proj}_X(𝒜)`. -/
abbrev space (P : Twist 𝒜 deg) : AlgebraicSpace S :=
  toAlgebraicSpace P.functor P.associated

/-- The structure morphism `π : P ⟶ X`. -/
abbrev π (P : Twist 𝒜 deg) : P.space ⟶ X :=
  toAlgebraicSpace_hom P.functor P.associated

/-- The canonical family of Serre twists `𝒪_P(n)`. -/
abbrev twistModule (P : Twist 𝒜 deg) : ℤ → P.space.Modules :=
  CanonicalTwists.obj P.functor P.associated

/-- The quasi-coherent `ℤ`-graded twist algebra `⊕_n 𝒪_P(n)`. -/
abbrev twistAlgebra (P : Twist 𝒜 deg) :
    GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift P.space) :=
  CanonicalTwists.algebra P.functor P.associated

/-- Universe lift identifies `𝒪_P(n)` with the degree-`n` piece of the twist algebra. -/
def twistModuleIso (P : Twist 𝒜 deg) (n : ℤ) :
    Modules.liftModule (P.twistModule n) ≅ P.twistAlgebra n :=
  (CanonicalTwists.family P.functor P.associated).iso n

/-- `twistModuleIso` is the comparison stored on the canonical twist family. -/
theorem twistModuleIso_eq (P : Twist 𝒜 deg) (n : ℤ) :
    twistModuleIso P n = (CanonicalTwists.family P.functor P.associated).iso n :=
  rfl

/-- Degree-`n` component of the canonical graded map `ψ : π^* 𝒜 ⟶ ⊕_{n ≥ 0} 𝒪_P(n)`. -/
abbrev canonicalHom (P : Twist 𝒜 deg) (n : ℕ) :
    (Modules.pullback P.π).obj (deg.obj n) ⟶ P.twistModule n :=
  (CanonicalTwists.psi P.functor P.associated).hom n

/-- `canonicalHom` is the degree-`n` component of `CanonicalTwists.psi`. -/
theorem canonicalHom_eq (P : Twist 𝒜 deg) (n : ℕ) :
    canonicalHom P n = (CanonicalTwists.psi P.functor P.associated).hom n :=
  rfl

/-- The degree-zero component sends the pulled-back unit of `𝒜` to the unit of `𝒪_P`. -/
theorem canonicalHom_map_one (P : Twist 𝒜 deg) :
    Modules.structureModulePullbackInv P.π ≫
        (Modules.pullback P.π).map (degreeZeroUnit deg) ≫
          P.canonicalHom 0 =
      CanonicalTwists.unit P.functor P.associated :=
  (CanonicalTwists.psi P.functor P.associated).map_one

/-- Homogeneous components of `ψ` preserve multiplication. -/
theorem canonicalHom_map_mul (P : Twist 𝒜 deg) (i j : ℕ) :
    pullbackTensorLax P.π (deg.obj i) (deg.obj j) ≫
        (Modules.pullback P.π).map (deg.mul i j) ≫
          P.canonicalHom (i + j) =
      CategoryTheory.MonoidalCategory.tensorHom (P.canonicalHom i) (P.canonicalHom j) ≫
        CanonicalTwists.mul P.functor P.associated (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg (CanonicalTwists.obj P.functor P.associated) (Int.natCast_add i j)) :=
  (CanonicalTwists.psi P.functor P.associated).map_mul i j

/-- The canonical integer-graded twist algebra is quasi-coherent. -/
theorem twistAlgebra_isQuasicoherent (P : Twist 𝒜 deg) : P.twistAlgebra.IsQuasicoherent :=
  _root_.AlgebraicGeometry.AlgebraicSpace.RelativeProj.algebra_isQuasicoherent P.functor P.associated

/-- The canonical degree-one map `π^* 𝒜_1 ⟶ 𝒪_P(1)`. -/
abbrev canonicalMap (P : Twist 𝒜 deg) :
    (Modules.pullback P.π).obj (deg.obj 1) ⟶ P.twistModule 1 :=
  P.canonicalHom 1

/-- `canonicalMap P` is the degree-one component of `canonicalHom`. -/
theorem canonicalMap_spec (P : Twist 𝒜 deg) :
    canonicalMap P = P.canonicalHom 1 :=
  rfl

/-- After every scheme base change, on every affine open and every positive-degree chart,
every nonnegative component of `ψ` agrees with Serre's homogeneous section map.
Stacks 01NR requires the square for each `A_n`, not only `A_1`. -/
def CanonicalHomAgreesWithTwistSection (P : Twist 𝒜 deg) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ X) (U : Z.left.affineOpens)
    (d : {k : ℕ // 1 ≤ k}) (n : ℕ),
    CanonicalTwists.affineChartPsiComparison g P.functor P.associated U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n =
      CanonicalTwists.affineChartPsiModel g P.functor P.associated U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n

/-- Every nonnegative degree of `ψ` agrees with the affine Serre model. -/
theorem canonicalHom_agrees_with_twistSection (P : Twist 𝒜 deg) {Z : Over S}
    (g : ofOver Z ⟶ X) (U : Z.left.affineOpens) (d : {k : ℕ // 1 ≤ k}) (n : ℕ) :
    CanonicalTwists.affineChartPsiComparison g P.functor P.associated U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n =
      CanonicalTwists.affineChartPsiModel g P.functor P.associated U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n :=
  psi_baseChange P.functor P.associated g U d n

/-- The local Serre comparison holds for every nonnegative degree, and the global components
are those of `CanonicalTwists.psi`. -/
theorem CanonicalHomAgreesWithTwistSection_iff (P : Twist 𝒜 deg) :
    CanonicalHomAgreesWithTwistSection P ↔
      (∀ n : ℕ,
          P.canonicalHom n = (CanonicalTwists.psi P.functor P.associated).hom n) ∧
        ∀ {Z : Over S} (g : ofOver Z ⟶ X) (U : Z.left.affineOpens)
          (d : {k : ℕ // 1 ≤ k}) (n : ℕ),
          CanonicalTwists.affineChartPsiComparison g P.functor P.associated U
              (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n =
            CanonicalTwists.affineChartPsiModel g P.functor P.associated U
              (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg P.functor U) d n := by
  constructor
  · intro h
    exact ⟨fun n => canonicalHom_eq P n, h⟩
  · intro h
    exact h.2

/-- The input hypotheses, quasi-coherence, and local formula of Stacks 01NR/01O0
hold for the canonical twists and every nonnegative component of `ψ`. -/
theorem conditions_spec (P : Twist 𝒜 deg) :
    𝒜.IsQuasicoherent ∧ 𝒜.IsCommutative ∧ P.twistAlgebra.IsQuasicoherent ∧
      (∀ n : ℤ, (CanonicalTwists.obj P.functor P.associated n).IsQuasicoherent) ∧
      (∀ n : ℕ, P.canonicalHom n = (CanonicalTwists.psi P.functor P.associated).hom n) ∧
      CanonicalHomAgreesWithTwistSection P :=
  ⟨algebra_isQuasicoherent P, algebra_isCommutative P, twistAlgebra_isQuasicoherent P,
    fun n => CanonicalTwists.obj_isQuasicoherent P.functor P.associated n,
    fun n => canonicalHom_eq P n, fun g U d n => canonicalHom_agrees_with_twistSection P g U d n⟩

end Twist

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
