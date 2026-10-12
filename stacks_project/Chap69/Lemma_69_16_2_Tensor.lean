/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec

/-!
# Tensor modules and direct image to Spec of global sections

The module is constructed on each etale scheme V over X as sections of the
ordinary scheme pullback of tilde M along V → Spec A. Restriction maps are
the genuine scheme pullback comparisons. No algebraic-space module inverse
image is chosen from an unproved adjoint-existence assertion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute map from an etale scheme V over X to Spec A, recovered by
Yoneda from its map to the graph target and then composed with the projection. -/
noncomputable def etaleToSpecA {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : smallEtaleSite X) : V.left.left ⟶ Spec (globalSectionsRing X) :=
  (yonedaEquiv (V.hom ≫ toSpecGamma X) : V.left ⟶ specGammaOver X).left ≫
    specGamma_fst X

/-- The scheme maps to Spec A commute with morphisms in the etale site. -/
theorem etaleToSpecA_naturality {S : Scheme.{u}} (X : AlgebraicSpace S)
    {V W : smallEtaleSite X} (f : V ⟶ W) :
    f.left.left ≫ etaleToSpecA X W = etaleToSpecA X V :=
  sorry

/-- The ordinary scheme pullback of tilde M on a scheme etale over X. -/
noncomputable def tensorOXOnEtale {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (V : smallEtaleSite X) :
    V.left.left.Modules :=
  (Scheme.Modules.pullback (etaleToSpecA X V)).obj (tildeOnSpec X M)

/-- The canonical comparison along an etale-site arrow is scheme pullback
composition followed by congruence of the actual maps to Spec A. -/
noncomputable def tensorOXEtaleRestriction {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) {V W : smallEtaleSite X} (f : V ⟶ W) :
    (Scheme.Modules.pullback f.left.left).obj (tensorOXOnEtale X M W) ⟶
      tensorOXOnEtale X M V :=
  (Scheme.Modules.pullbackComp f.left.left (etaleToSpecA X W)).hom.app (tildeOnSpec X M) ≫
    (Scheme.Modules.pullbackCongr (etaleToSpecA_naturality X f)).hom.app (tildeOnSpec X M)

/-- On an etale scheme V the tensor presheaf has sections Gamma(V,p_V^* tilde M).
Its maps first pull sections back and then apply the specified comparison. -/
noncomputable def tensorOXPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) : PresheafOfModules.{u} (structureSheaf X).obj where
  obj V := (tensorOXOnEtale X M V.unop).val.obj (op ⊤)
  map {V W} f :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f.unop.left.left).unit.app
      (tensorOXOnEtale X M V.unop)).val.app (op ⊤) ≫
    (ModuleCat.restrictScalars ((structureSheaf X).obj.map f).hom).map
      ((tensorOXEtaleRestriction X M f.unop).val.app (op ⊤))
  map_id := sorry
  map_comp := sorry

/-- Sections of these compatible quasi-coherent scheme pullbacks satisfy
etale descent; this is the sheaf law for the already specified presheaf. -/
theorem tensorOXPresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    Presheaf.IsSheaf (smallEtaleTopology X) (tensorOXPresheaf X M).presheaf :=
  sorry

/-- The module M tensor_A O_X, with explicit values and restrictions on the
small etale site, computed by ordinary scheme pullbacks of tilde M. -/
noncomputable def tensorOX {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) : X.Modules :=
  ⟨tensorOXPresheaf X M, tensorOXPresheaf_isSheaf X M⟩

/-- The displayed sheaf is quasi-coherent, since on etale schemes it is the
usual scheme pullback of the quasi-coherent associated module. -/
instance instIsQuasicoherent_tensorOX {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) : (tensorOX X M).IsQuasicoherent :=
  sorry

/-- The global section associated with m is its pullback from the affine
tilde module on every etale scheme V over X, namely 1 tensor m. -/
noncomputable def tensorOXUnitSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (m : M) : (tensorOX X M).sections :=
  ⟨fun V ↦
    (Scheme.Modules.globalSectionsPullback (etaleToSpecA X V.unop) (tildeOnSpec X M)).hom
      ((AlgebraicGeometry.tilde.isoTop M).hom.hom m), sorry⟩

/-- A compatible section gives a constant-vertex cone over the right-Kan
diagram used by the explicit direct image on type-valued sheaves. -/
noncomputable def directImageSectionCone {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections)
    (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
      (SpacesEtale.AtlasCharts.inclusion X).op ⋙ ((EtaleTopos.smallEquivalence X).functor.obj F).obj) where
  pt := PUnit
  π := { app := fun a ↦ TypeCat.ofHom
           (fun _ ↦ s.1 (op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)))
         naturality := sorry }

/-- Direct image of a compatible section, formed by the explicit limit lift
in each right-Kan fiber, rather than by a chosen inverse-image adjunction. -/
noncomputable def typeDirectImageSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) (Type u)) (s : F.obj.sections) :
    ((typePushforward f).obj F).obj.sections :=
  ⟨fun V ↦
      (((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj F).obj
      (op ((etaleBaseChange f).obj V.unop))).inv
        ((limit.lift _ (directImageSectionCone f F s V.unop)) PUnit.unit)), sorry⟩

/-- The direct image of a module section uses the specified type-valued
direct image and the actual forgetful comparison for module direct image. -/
noncomputable def moduleDirectImageSection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (s : F.sections) :
    ((Modules.pushforward f).obj F).sections :=
  let t := typeDirectImageSection f
    ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj F) s
  ⟨fun V ↦
    (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app F).hom.app V)
      (t.1 V), sorry⟩

/-- Absolute direct image to Spec A: graph direct image, etale-to-Zariski
direct image, then direct image along the scheme projection. -/
noncomputable def toSpecAPushforward {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ (Spec (globalSectionsRing X)).Modules :=
  Modules.pushforward (toSpecGamma X) ⋙ Modules.toScheme (specGammaOver X) ⋙
    Scheme.Modules.pushforward (specGamma_fst X)

/-- Global sections with the A-action supplied by the actual absolute map
to Spec A and Mathlib's affine module global-sections functor. -/
noncomputable def moduleGlobalSections {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) : ModuleCat.{u} (globalSectionsRing X) :=
  (moduleSpecΓFunctor (R := globalSectionsRing X)).obj ((toSpecAPushforward X).obj F)

/-- The etale object selected by the inverse image of the whole Spec A
under the projection and the two explicit site comparison functors. -/
noncomputable def specAGlobalEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite (specGamma X) :=
  (schemeEtaleRingedHom (specGammaOver X)).base.obj
    ((smallEtaleToOpensRingedHom (specGammaOver X).left).base.obj
      ((specGamma_fst X) ⁻¹ᵁ ⊤))

/-- Evaluate the direct image of a compatible section at the open pulled
back from the whole Spec A, through the two explicit site comparison functors. -/
noncomputable def toSpecAGlobalSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) (s : F.sections) : moduleGlobalSections X F :=
  (moduleDirectImageSection (toSpecGamma X) F s).1 (op (specAGlobalEtale X))

/-- The canonical A-linear comparison m maps to the compatible sections
1 tensor m, followed by actual direct image to Spec A and top-open evaluation. -/
noncomputable def tensorOXSectionsUnit {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    M ⟶ moduleGlobalSections X (tensorOX X M) :=
  @ModuleCat.ofHom (globalSectionsRing X) _ M (moduleGlobalSections X (tensorOX X M))
    M.isAddCommGroup M.isModule
    (moduleGlobalSections X (tensorOX X M)).isAddCommGroup
    (moduleGlobalSections X (tensorOX X M)).isModule
    { toFun := fun m ↦ toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M m)
      map_add' := sorry
      map_smul' := sorry }

/-- The comparison tilde M to p_*(M tensor O_X) is the transpose of the
specified section map under Mathlib's proved tilde-global-sections adjunction. -/
noncomputable def tensorOXPushforwardUnit {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    tildeOnSpec X M ⟶ (toSpecAPushforward X).obj (tensorOX X M) :=
  ((AlgebraicGeometry.tilde.adjunction (R := globalSectionsRing X)).homEquiv M
    ((toSpecAPushforward X).obj (tensorOX X M))).symm (tensorOXSectionsUnit X M)

end AlgebraicGeometry.AlgebraicSpace
