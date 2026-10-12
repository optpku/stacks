/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Chaotic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.CategoryTheory.Sites.Chaotic
public import stacks_project.Chap96.«96_24_3_1_Comparison»

/-!
# Quasi-coherent modules on the associated affine site

An `𝒪`-module on `𝒳_affine` is a module presheaf over the universe-lifted
commutative structure presheaf of the affine inclusion. Cartesianness is
base-change compatibility of sections; quasi-coherence is Mathlib's local
presentation predicate on the chaotic site, on each associated affine
`τ`-site, and after transport along the ringed-topos comparison of 96.24.3.1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Presheaf
open SheafOfModules SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The universe-lifted commutative structure presheaf `𝒪` on `𝒳_affine`. -/
def affineCommPresheaf (X : GroupoidsOver S) :
    (Affine X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Scheme.Over.commStructurePresheaf (affineInclusion X ⋙ X.p)

/-- Objectwise, `affineCommPresheaf X` is the universe lift of global sections of
the scheme underlying an affine object. -/
theorem affineCommPresheaf_obj (X : GroupoidsOver S) (x : Affine X) :
    (affineCommPresheaf X).obj (op x) =
      CommRingCat.of
        (ULift.{u + 1, u} ((Scheme.Γ.obj (op (X.p.obj x.obj).left)))) :=
  sorry

/-- The chaotic commutative structure sheaf on `𝒳_affine`. -/
def affineCommStructureSheaf (X : GroupoidsOver S) :
    Sheaf (affineTopology X) CommRingCat.{u + 1} :=
  ⟨affineCommPresheaf X, Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of `affineCommStructureSheaf X` is `affineCommPresheaf X`. -/
theorem affineCommStructureSheaf_obj (X : GroupoidsOver S) :
    (affineCommStructureSheaf X).obj = affineCommPresheaf X :=
  sorry

/-- `affineCommStructureSheaf X` is the chaotic sheaf packaging of `affineCommPresheaf X`. -/
theorem affineCommStructureSheaf_eq (X : GroupoidsOver S) :
    affineCommStructureSheaf X =
      ⟨affineCommPresheaf X, Presheaf.isSheaf_bot _⟩ :=
  sorry

/-- Presheaves of `𝒪`-modules on `𝒳_affine`. -/
abbrev AffineModule (X : GroupoidsOver S) :=
  PresheafOfModules.{u + 1} (ringPresheafOfComm (affineCommPresheaf X))

namespace AffineModule

/-- Evaluation of an affine module at an object of `𝒳_affine`. -/
abbrev eval {X : GroupoidsOver S} (F : AffineModule X) (x : Affine X) :=
  F.obj (op x)

/-- Evaluation of an affine module is the module presheaf at the opposite object. -/
theorem eval_eq {X : GroupoidsOver S} (F : AffineModule X) (x : Affine X) :
    F.eval x = F.obj (op x) :=
  sorry

/-- The canonical comparison `F(x') ⊗[𝒪(x')] 𝒪(x) ⟶ F(x)` attached to
`f : x ⟶ x'` in `𝒳_affine`. -/
def baseChangeMap {X : GroupoidsOver S} (F : AffineModule X)
    {x x' : Affine X} (f : x ⟶ x') :
    (PresheafOfModules.BaseChange.functor.{u + 1, u, u + 1, 0}
        (affineCommPresheaf X) f.op).obj F ⟶
      F.eval x :=
  PresheafOfModules.BaseChange.map.{u + 1, u, u + 1, 0}
    (affineCommPresheaf X) F f.op

/-- The named affine base-change map is the canonical presheaf comparison. -/
theorem baseChangeMap_def {X : GroupoidsOver S} (F : AffineModule X)
    {x x' : Affine X} (f : x ⟶ x') :
    F.baseChangeMap f =
      PresheafOfModules.BaseChange.map.{u + 1, u, u + 1, 0}
        (affineCommPresheaf X) F f.op :=
  sorry

/-- Weak sheafification exists on every slice of the chaotic affine topology. -/
instance hasWeakSheafify_affineTopology_over (X : GroupoidsOver S) (x : Affine X) :
    HasWeakSheafify ((affineTopology X).over x) AddCommGrpCat.{u + 1} :=
  sorry

/-- Local bijectivity characterizes sheafification on chaotic affine slices. -/
instance wEqualsLocallyBijective_affineTopology_over (X : GroupoidsOver S)
    (x : Affine X) :
    ((affineTopology X).over x).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Ring-to-abelian-group sheaf composition exists on chaotic affine slices. -/
instance hasSheafCompose_affineTopology_over_ring_addCommGrp
    (X : GroupoidsOver S) (x : Affine X) :
    ((affineTopology X).over x).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- The chaotic module sheaf associated to a module presheaf on `𝒳_affine`. -/
def asChaoticSheaf {X : GroupoidsOver S} (F : AffineModule X) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (affineTopology X) (affineCommStructureSheaf X) :=
  ⟨F, Presheaf.isSheaf_bot _⟩

/-- The underlying module presheaf of `asChaoticSheaf F` is `F`. -/
theorem asChaoticSheaf_val {X : GroupoidsOver S} (F : AffineModule X) :
    (asChaoticSheaf F).val = F :=
  sorry

/-- An affine module is cartesian when every scalar-extension comparison is an
isomorphism. -/
def IsCartesian {X : GroupoidsOver S} (F : AffineModule X) : Prop :=
  PresheafOfModules.BaseChange.compatible.{u + 1, u, u + 1, 0}
    (affineCommPresheaf X) F

/-- Cartesianness is the pointwise isomorphism condition for affine base-change maps. -/
theorem isCartesian_iff {X : GroupoidsOver S} (F : AffineModule X) :
    F.IsCartesian ↔
      ∀ ⦃x x' : Affine X⦄ (f : x ⟶ x'), IsIso (F.baseChangeMap f) :=
  sorry

/-- Quasi-coherence of an affine module on the chaotic ringed site
`(𝒳_affine, 𝒪)`, in the sense of Modules on Sites, Definition 18.23.1. -/
def IsQuasicoherent {X : GroupoidsOver S} (F : AffineModule X) : Prop :=
  (asChaoticSheaf F).IsQuasicoherent

/-- Chaotic quasi-coherence is quasi-coherence of the associated chaotic module sheaf. -/
theorem isQuasicoherent_iff {X : GroupoidsOver S} (F : AffineModule X) :
    F.IsQuasicoherent ↔ (asChaoticSheaf F).IsQuasicoherent :=
  sorry

end AffineModule

/-- The commutative structure presheaf on `𝒳_affine` is a sheaf for every
associated affine `τ`-topology. -/
theorem affineCommPresheaf_isSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Presheaf.IsSheaf (X.associatedAffineTopology τ) (affineCommPresheaf X) :=
  sorry

/-- The commutative structure sheaf `𝒪` on the associated affine `τ`-site. -/
def affineCommSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (X.associatedAffineTopology τ) CommRingCat.{u + 1} :=
  ⟨affineCommPresheaf X, affineCommPresheaf_isSheaf X τ⟩

/-- The underlying presheaf of `affineCommSheaf X τ` is `affineCommPresheaf X`. -/
theorem affineCommSheaf_obj (X : GroupoidsOver S) (τ : StandardTopology) :
    (affineCommSheaf X τ).obj = affineCommPresheaf X :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists on every associated affine
`τ`-topology. -/
instance hasSheafCompose_associatedAffineCommRing (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (X.associatedAffineTopology τ).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Weak sheafification exists on every slice of an associated affine `τ`-topology. -/
instance hasWeakSheafify_associatedAffineTopology_over (X : GroupoidsOver S)
    (τ : StandardTopology) (x : Affine X) :
    HasWeakSheafify ((X.associatedAffineTopology τ).over x)
      AddCommGrpCat.{u + 1} :=
  sorry

/-- Local bijectivity characterizes sheafification on associated affine slices. -/
instance wEqualsLocallyBijective_associatedAffineTopology_over
    (X : GroupoidsOver S) (τ : StandardTopology) (x : Affine X) :
    ((X.associatedAffineTopology τ).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  sorry

/-- Ring-to-abelian-group sheaf composition exists on associated affine slices. -/
instance hasSheafCompose_associatedAffineTopology_over_ring_addCommGrp
    (X : GroupoidsOver S) (τ : StandardTopology) (x : Affine X) :
    ((X.associatedAffineTopology τ).over x).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

namespace AffineModule

/-- Quasi-coherence of an affine module for a standard topology `τ`: the
presheaf is a `τ`-sheaf and the resulting module sheaf is quasi-coherent. -/
def IsQuasicoherentFor {X : GroupoidsOver S} (F : AffineModule X)
    (τ : StandardTopology) : Prop :=
  ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology τ) F.presheaf,
    (⟨F, hF⟩ : SheafOfModules.{u + 1}
      (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
        (affineCommSheaf X τ))).IsQuasicoherent

/-- The affine `τ`-quasi-coherence predicate records sheafhood and quasi-coherence
together. -/
theorem isQuasicoherentFor_iff {X : GroupoidsOver S} (F : AffineModule X)
    (τ : StandardTopology) :
    F.IsQuasicoherentFor τ ↔
      ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology τ) F.presheaf,
        (⟨F, hF⟩ : SheafOfModules.{u + 1}
          (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
            (affineCommSheaf X τ))).IsQuasicoherent :=
  sorry

end AffineModule

/-- Universe lifting of commutative rings commutes with forgetting to rings. -/
def universeLiftForget₂Iso :
    CommRingCat.universeLift.{u, u + 1} ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ≅
      forget₂ CommRingCat.{u} RingCat.{u} ⋙
        Scheme.Site.ringUniverseLift.{u, u + 1} where
  hom := { app := fun R ↦ 𝟙 _, naturality := sorry }
  inv := { app := fun R ↦ 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `universeLiftForget₂Iso` is the identity on each object. -/
theorem universeLiftForget₂Iso_app (R : CommRingCat.{u}) :
    universeLiftForget₂Iso.hom.app R = 𝟙 _ :=
  sorry

/-- The underlying ring presheaf of `affineCommSheaf` is the restriction of the
lifted structure sheaf along the affine inclusion. -/
def affineRingPresheafIso (X : GroupoidsOver S) (τ : StandardTopology) :
    (CategoryTheory.Sheaf.ringSheafOfComm (affineCommSheaf X τ)).obj ≅
      (associatedAffineStructureSheaf X τ).obj :=
  Functor.isoWhiskerLeft
    ((affineInclusion X ⋙ X.p).op ⋙ (Over.forget S).op ⋙ Scheme.Γ)
    universeLiftForget₂Iso

/-- `affineRingPresheafIso` is whiskering of `universeLiftForget₂Iso` along global
sections of the restricted projection. -/
theorem affineRingPresheafIso_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    affineRingPresheafIso X τ =
      Functor.isoWhiskerLeft
        ((affineInclusion X ⋙ X.p).op ⋙ (Over.forget S).op ⋙ Scheme.Γ)
        universeLiftForget₂Iso :=
  sorry

/-- Identification of the commutative and ring presentations of `𝒪` on the
associated affine `τ`-site. -/
def affineRingSheafIso (X : GroupoidsOver S) (τ : StandardTopology) :
    CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (affineCommSheaf X τ) ≅
      associatedAffineStructureSheaf X τ where
  hom := Sheaf.homEquiv.symm (affineRingPresheafIso X τ).hom
  inv := Sheaf.homEquiv.symm (affineRingPresheafIso X τ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying presheaf morphism of `affineRingSheafIso` is
`affineRingPresheafIso`. -/
theorem affineRingSheafIso_hom (X : GroupoidsOver S) (τ : StandardTopology) :
    (affineRingSheafIso X τ).hom.hom = (affineRingPresheafIso X τ).hom :=
  sorry

/-- Type-valued sheafification exists on every associated affine `τ`-topology. -/
instance hasSheafify_associatedAffineTopology (X : GroupoidsOver S)
    (τ : StandardTopology) :
    HasSheafify (X.associatedAffineTopology τ) (Type (u + 1)) :=
  sorry

/-- Pointwise right Kan extension along the opposite affine inclusion exists. -/
instance hasPointwiseRightKanExtension_affineInclusion (X : GroupoidsOver S)
    (P : (Affine X)ᵒᵖ ⥤ Type (u + 1)) :
    (affineInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Ring-valued sheaf composition exists on every associated affine `τ`-topology. -/
instance hasSheafCompose_associatedAffineTopology_forgetRing
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1}) :=
  sorry

/-- Ring-valued sheaf composition exists on every associated `τ`-topology of `X`. -/
instance hasSheafCompose_associatedTopology_forgetRing
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1}) :=
  sorry

/-- Weak sheafification exists on every slice of an associated `τ`-topology. -/
instance hasWeakSheafify_associatedTopology_over (X : GroupoidsOver S)
    (τ : StandardTopology) (x : X.total) :
    HasWeakSheafify ((X.associatedTopology τ).over x) AddCommGrpCat.{u + 1} :=
  sorry

/-- Local bijectivity characterizes sheafification on associated `τ`-slices. -/
instance wEqualsLocallyBijective_associatedTopology_over
    (X : GroupoidsOver S) (τ : StandardTopology) (x : X.total) :
    ((X.associatedTopology τ).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  sorry

/-- Ring-to-abelian-group sheaf composition exists on associated `τ`-slices. -/
instance hasSheafCompose_associatedTopology_over_ring_addCommGrp
    (X : GroupoidsOver S) (τ : StandardTopology) (x : X.total) :
    ((X.associatedTopology τ).over x).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

namespace AffineModule

/-- Transport an affine `τ`-module sheaf to the ring presentation of `𝒪` used by
the comparison of 96.24.3.1. -/
def toAssociatedModule {X : GroupoidsOver S} (F : AffineModule X)
    {τ : StandardTopology}
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology τ) F.presheaf) :
    SheafOfModules (associatedAffineStructureSheaf X τ) :=
  (SheafOfModules.restrictScalars (affineRingSheafIso X τ).inv).obj ⟨F, hF⟩

/-- Transport along `affineRingSheafIso` does not change the underlying abelian
presheaf. -/
theorem toAssociatedModule_val {X : GroupoidsOver S} (F : AffineModule X)
    {τ : StandardTopology}
    (hF : Presheaf.IsSheaf (X.associatedAffineTopology τ) F.presheaf) :
    (toAssociatedModule F hF).val.presheaf = F.presheaf :=
  sorry

/-- An affine module corresponds to a quasi-coherent module on `𝒳` via the
ringed-topos equivalence of 96.24.3.1 at the fppf topology. -/
def CorrespondsToQuasicoherent {X : GroupoidsOver S} (F : AffineModule X) :
    Prop :=
  ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology .fppf) F.presheaf,
    ((associatedAffineComparison X .fppf).modulePushforward.obj
      (toAssociatedModule F hF)).IsQuasicoherent

/-- Correspondence records fppf sheafhood together with quasi-coherence of the
module pushforward along `associatedAffineComparison` at fppf. -/
theorem correspondsToQuasicoherent_iff {X : GroupoidsOver S}
    (F : AffineModule X) :
    F.CorrespondsToQuasicoherent ↔
      ∃ hF : Presheaf.IsSheaf (X.associatedAffineTopology .fppf) F.presheaf,
        ((associatedAffineComparison X .fppf).modulePushforward.obj
          (toAssociatedModule F hF)).IsQuasicoherent :=
  sorry

end AffineModule

end AlgebraicGeometry.GroupoidsOver
