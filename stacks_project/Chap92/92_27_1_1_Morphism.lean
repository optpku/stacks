/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap92.«92_27_1_1_Object»

/-!
# Structure sheaves and morphisms of ringed topoi on `C_{X/Λ}`

This leaf owns the inherited étale topology on `category Λ X`, the sheaves
`O : (U ⟶ A) ↦ Γ(A, 𝒪_A)` and `underline{𝒪}_X = π⁻¹ 𝒪_X : (U ⟶ A) ↦ 𝒪_X(U)`, and
the morphisms of ringed topoi `i` (identity on topoi) and `π` induced by
`forget Λ X : category Λ X ⥤ smallEtaleSite X`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The topology on `C_{X/Λ}` inherited from the small étale topology of `X` along `forget`. -/
abbrev topology : GrothendieckTopology (category Λ X) :=
  (forget Λ X).inheritedTopology (smallEtaleTopology X)

/-- The topology on `C_{X/Λ}` is the inherited topology of `forget Λ X`. -/
theorem topology_eq :
    topology Λ X = (forget Λ X).inheritedTopology (smallEtaleTopology X) :=
  sorry

/-- The underlying presheaf of `O`, sending `(U ⟶ A)` to `Γ(A, 𝒪_A)`. -/
def structurePresheaf : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineScheme Λ X).op ⋙ Scheme.Γ

/-- The underlying presheaf of `underline{𝒪}_X`, sending `(U ⟶ A)` to `𝒪_X(U)`. -/
def underlinePresheaf : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (forget Λ X).op ⋙ commStructurePresheaf X

/-- The global-sections presheaf on affine-space vertices is a sheaf for the inherited
topology. -/
theorem structurePresheaf_isSheaf : Presheaf.IsSheaf (topology Λ X) (structurePresheaf Λ X) :=
  sorry

/-- The pulled-back structure presheaf of `X` is a sheaf for the inherited topology. -/
theorem underlinePresheaf_isSheaf : Presheaf.IsSheaf (topology Λ X) (underlinePresheaf Λ X) :=
  sorry

/-- The structure sheaf `O` on `C_{X/Λ}`, sending `(U ⟶ A)` to `Γ(A, 𝒪_A)`. -/
def structureSheaf : Sheaf (topology Λ X) CommRingCat.{u} :=
  ⟨structurePresheaf Λ X, structurePresheaf_isSheaf Λ X⟩

/-- The sheaf `underline{𝒪}_X = π⁻¹ 𝒪_X` on `C_{X/Λ}`, sending `(U ⟶ A)` to `𝒪_X(U)`. -/
def underlineSheaf : Sheaf (topology Λ X) CommRingCat.{u} :=
  ⟨underlinePresheaf Λ X, underlinePresheaf_isSheaf Λ X⟩

/-- The value of `O` at `(U ⟶ A)` is the global-sections ring of `A`. -/
theorem structureSheaf_obj (x : category Λ X) :
    (structureSheaf Λ X).obj.obj (op x) = CommRingCat.of Γ(x.right.obj.left, ⊤) :=
  sorry

/-- The value of `underline{𝒪}_X` at `(U ⟶ A)` is the value of `𝒪_X` at `U`. -/
theorem underlineSheaf_obj (x : category Λ X) :
    (underlineSheaf Λ X).obj.obj (op x) = (commStructurePresheaf X).obj (op x.left) :=
  sorry

/-- The sheaf morphism `i♯ : O ⟶ underline{𝒪}_X` whose component at `(U ⟶ A)` is
`Scheme.Γ.map` of the underlying scheme morphism of `x.hom : U ⟶ A`. -/
def structureSheafMap : structureSheaf Λ X ⟶ underlineSheaf Λ X :=
  ObjectProperty.homMk
    { app := fun P ↦ Scheme.Γ.map (op (unop P).hom.left)
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `i♯` at `(U ⟶ A)` is `Scheme.Γ.map` of the underlying map of `x.hom`. -/
theorem structureSheafMap_app (x : category Λ X) :
    (structureSheafMap Λ X).hom.app (op x) = Scheme.Γ.map (op x.hom.left) :=
  sorry

/-- `O`, lifted to `CommRingCat.{u + 1}` for the ringed-topos presentation. -/
def structurePresheafLift : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  structurePresheaf Λ X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- `underline{𝒪}_X`, lifted to `CommRingCat.{u + 1}` for the ringed-topos presentation. -/
def underlinePresheafLift : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  underlinePresheaf Λ X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted global-sections presheaf on affine-space vertices is a sheaf. -/
theorem structurePresheafLift_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (structurePresheafLift Λ X) :=
  sorry

/-- The lifted inverse-image presheaf of `𝒪_X` is a sheaf. -/
theorem underlinePresheafLift_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (underlinePresheafLift Λ X) :=
  sorry

/-- The universe-lifted structure sheaf `O` on `C_{X/Λ}`. -/
def structureSheafLift : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  ⟨structurePresheafLift Λ X, structurePresheafLift_isSheaf Λ X⟩

/-- The universe-lifted sheaf `underline{𝒪}_X` on `C_{X/Λ}`. -/
def underlineSheafLift : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  ⟨underlinePresheafLift Λ X, underlinePresheafLift_isSheaf Λ X⟩

/-- The lifted structure map `i♯`. -/
def structureSheafMapLift : structureSheafLift Λ X ⟶ underlineSheafLift Λ X :=
  ObjectProperty.homMk
    { app := fun P ↦
        (CommRingCat.universeLift.{u, u + 1}).map ((structureSheafMap Λ X).hom.app P)
      naturality := fun _ _ _ ↦ sorry }

/-- Commutative-ring-valued sheaf composition exists on the inherited topology of `C_{X/Λ}`. -/
instance topology_hasSheafCompose_comm :
    (topology Λ X).HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Ring-valued sheaf composition exists on the inherited topology of `C_{X/Λ}`. -/
instance topology_hasSheafCompose_forget :
    (topology Λ X).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) :=
  sorry

/-- Ring-valued sheaf composition exists on the small étale topology of `X` in universe
`u + 1`. -/
instance smallEtaleTopology_hasSheafCompose_forget :
    (smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) :=
  sorry

/-- Type-valued sheafification exists on the inherited topology of `C_{X/Λ}`. -/
instance topology_hasSheafify : HasSheafify (topology Λ X) (Type (u + 1)) :=
  sorry

/-- Pointwise right Kan extensions along `forget.op` exist in universe `u + 1`. -/
instance forget_op_hasPointwiseRightKanExtension (P : (category Λ X)ᵒᵖ ⥤ Type (u + 1)) :
    (forget Λ X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The ring-valued underlying presheaf of the lifted structure sheaf `O`. -/
def structurePresheafRing : (category Λ X)ᵒᵖ ⥤ RingCat.{u + 1} :=
  structurePresheafLift Λ X ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The ring-valued inverse image of `𝒪_X` along `forget`. -/
def underlinePresheafRing : (category Λ X)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (forget Λ X).op ⋙ (commRingedSiteLift X).structureSheaf.obj

/-- The ring-valued presheaf of `O` is a sheaf. -/
theorem structurePresheafRing_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (structurePresheafRing Λ X) :=
  sorry

/-- The ring-valued inverse image of `𝒪_X` is a sheaf. -/
theorem underlinePresheafRing_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (underlinePresheafRing Λ X) :=
  sorry

/-- The ring-valued structure sheaf `O` on `C_{X/Λ}`. -/
def structureSheafRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  ⟨structurePresheafRing Λ X, structurePresheafRing_isSheaf Λ X⟩

/-- The ring-valued sheaf `underline{𝒪}_X` on `C_{X/Λ}`. -/
def underlineSheafRing : Sheaf (topology Λ X) RingCat.{u + 1} :=
  ⟨underlinePresheafRing Λ X, underlinePresheafRing_isSheaf Λ X⟩

/-- The ring-valued structure map `i♯`, obtained by forgetting commutativity of
`structureSheafMapLift`. -/
def structureSheafMapRing : structureSheafRing Λ X ⟶ underlineSheafRing Λ X :=
  ObjectProperty.homMk
    { app := fun P ↦
        (CategoryTheory.forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
          ((structureSheafMapLift Λ X).hom.app P)
      naturality := fun _ _ _ ↦ sorry }

/-- The ringed site `(Sh(C_{X/Λ}), O)`. -/
def ringedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (topology Λ X) (structureSheafRing Λ X)

/-- The ringed site `(Sh(C_{X/Λ}), underline{𝒪}_X)`. -/
def underlineRingedSite : RingedSite.{u + 1, u, u + 1} :=
  ofRingSheaf (topology Λ X) (underlineSheafRing Λ X)

/-- The same-site morphism of ringed sites with identity base functor and structure map `i♯`. -/
def sameSite : underlineRingedSite Λ X ⟶ ringedSite Λ X :=
  SameSite.hom (structureSheafMapRing Λ X)

/-- The morphism of ringed topoi `i : (Sh(C), underline{𝒪}_X) ⟶ (Sh(C), O)`, identity on
underlying topoi, with `i♯ : O ⟶ underline{𝒪}_X` the obvious map. -/
def i : ToposHom (underlineRingedSite Λ X) (ringedSite Λ X) :=
  Hom.toToposHom (sameSite Λ X)

/-- The forgetful functor `u : C_{X/Λ} ⥤ X_étale` as a functor of ringed-site carriers. -/
def forgetOnSites : underlineRingedSite Λ X ⥤ commRingedSiteLift X :=
  forget Λ X

/-- The inverse-image comparison identifying `forget⁻¹ 𝒪_X` with `underline{𝒪}_X`. -/
def underlineComparison :
    (forgetOnSites Λ X).op ⋙ (commRingedSiteLift X).structureSheaf.obj ⟶
      (underlineRingedSite Λ X).structureSheaf.obj :=
  𝟙 (underlinePresheafRing Λ X)

/-- The forgetful functor is cocontinuous from the inherited topology to the small étale
topology. -/
instance forgetOnSites_isCocontinuous :
    (forgetOnSites Λ X).IsCocontinuous
      (underlineRingedSite Λ X).siteTopology (commRingedSiteLift X).siteTopology :=
  sorry

/-- Pointwise right Kan extensions along `forgetOnSites.op` exist in universe `u + 1`. -/
instance forgetOnSites_op_hasPointwiseRightKanExtension
    (P : (underlineRingedSite Λ X)ᵒᵖ ⥤ Type (u + 1)) :
    (forgetOnSites Λ X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Type-valued sheafification exists on the ringed site `(Sh(C), underline{𝒪}_X)`. -/
instance underlineRingedSite_hasSheafify :
    HasSheafify (underlineRingedSite Λ X).siteTopology (Type (u + 1)) :=
  sorry

/-- Ring-valued sheaf composition exists on `(Sh(C), underline{𝒪}_X)`. -/
instance underlineRingedSite_hasSheafCompose :
    (underlineRingedSite Λ X).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) :=
  sorry

/-- Ring-valued sheaf composition exists on the lifted small étale ringed site of `X`. -/
instance commRingedSiteLift_hasSheafCompose :
    (commRingedSiteLift X).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{u + 1}) :=
  sorry

/-- The morphism of ringed topoi `π : (Sh(C), underline{𝒪}_X) ⟶ (Sh(X_étale), 𝒪_X)` induced
by the forgetful functor `u : C_{X/Λ} ⥤ X_étale`. -/
def π : ToposHom (underlineRingedSite Λ X) (commRingedSiteLift X) :=
  Cocontinuous.toRingedTopos (forgetOnSites Λ X) (underlineComparison Λ X)

/-- The base functor of `i` is the identity of `C_{X/Λ}`. -/
theorem i_base : (sameSite Λ X).base = 𝟭 (category Λ X) :=
  sorry

/-- Inverse image of `𝒪_X` along `forget` recovers `underline{𝒪}_X` on underlying
presheaves. -/
theorem forget_inverseImage_structure :
    underlinePresheafRing Λ X = (underlineRingedSite Λ X).structureSheaf.obj :=
  sorry

/-- The underlying functor of `π` is the forgetful functor `forget Λ X`. -/
theorem π_base : forgetOnSites Λ X = forget Λ X :=
  sorry

/-- The structure-presheaf comparison of `π` is the identity identifying `forget⁻¹ 𝒪_X`
with `underline{𝒪}_X`. -/
theorem π_structureMap :
    underlineComparison Λ X = 𝟙 (underlinePresheafRing Λ X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
