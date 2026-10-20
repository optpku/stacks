/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent

/-! # Modules associated to modules over global sections -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat TopCat AlgebraicGeometry
open TopologicalSpace
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
  (Scheme.Modules.pullback (etaleToSpecA X V)).obj ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M)

/-- The canonical comparison along an etale-site arrow is scheme pullback
composition followed by congruence of the actual maps to Spec A. -/
noncomputable def tensorOXEtaleRestriction {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) {V W : smallEtaleSite X} (f : V ⟶ W) :
    (Scheme.Modules.pullback f.left.left).obj (tensorOXOnEtale X M W) ⟶
      tensorOXOnEtale X M V :=
  (Scheme.Modules.pullbackComp f.left.left (etaleToSpecA X W)).hom.app ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M) ≫
    (Scheme.Modules.pullbackCongr (etaleToSpecA_naturality X f)).hom.app ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M)

/-- Restriction of associated-module sections along a morphism of étale charts. -/
noncomputable def tensorOXPresheafMap {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X))
    {V W : (smallEtaleSite X)ᵒᵖ} (f : V ⟶ W) :
    (tensorOXOnEtale X M V.unop).val.obj (op ⊤) ⟶
      (ModuleCat.restrictScalars ((structureSheaf X).obj.map f).hom).obj
        ((tensorOXOnEtale X M W.unop).val.obj (op ⊤)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f.unop.left.left).unit.app
    (tensorOXOnEtale X M V.unop)).val.app (op ⊤) ≫
  (ModuleCat.restrictScalars ((structureSheaf X).obj.map f).hom).map
    ((tensorOXEtaleRestriction X M f.unop).val.app (op ⊤))

private theorem tensorOXPresheaf_map_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (V : (smallEtaleSite X)ᵒᵖ) :
    tensorOXPresheafMap X M (𝟙 V) =
      (ModuleCat.restrictScalarsId' ((structureSheaf X).obj.map (𝟙 V)).hom
        (congrArg RingCat.Hom.hom ((structureSheaf X).obj.map_id V))).inv.app _ :=
  sorry

private theorem tensorOXPresheaf_map_comp {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) {V W Z : (smallEtaleSite X)ᵒᵖ}
    (f : V ⟶ W) (g : W ⟶ Z) :
    tensorOXPresheafMap X M (f ≫ g) =
      tensorOXPresheafMap X M f ≫ (ModuleCat.restrictScalars _).map
        (tensorOXPresheafMap X M g) ≫
      (ModuleCat.restrictScalarsComp' ((structureSheaf X).obj.map f).hom
        ((structureSheaf X).obj.map g).hom ((structureSheaf X).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((structureSheaf X).obj.map_comp f g))).inv.app _ :=
  sorry

/-- On an étale chart the associated-module presheaf consists of sections of the
scheme pullback, with restrictions induced by pullback composition. -/
noncomputable def tensorOXPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) : PresheafOfModules.{u} (structureSheaf X).obj where
  obj V := (tensorOXOnEtale X M V.unop).val.obj (op ⊤)
  map f := tensorOXPresheafMap X M f
  map_id := by exact tensorOXPresheaf_map_id X M
  map_comp := by exact tensorOXPresheaf_map_comp X M

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

/-- The value of the associated module on a chart is the top-open section module
of the corresponding scheme pullback. -/
theorem tensorOX_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (V : (smallEtaleSite X)ᵒᵖ) :
    (tensorOX X M).val.obj V = (tensorOXOnEtale X M V.unop).val.obj (op ⊤) :=
  rfl

private theorem tensorOXUnitSection_compatible {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (m : M) :
    (fun (V : (smallEtaleSite X)ᵒᵖ) ↦ (Scheme.Modules.globalSectionsPullback (etaleToSpecA X V.unop)
        ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M)).hom
      ((AlgebraicGeometry.tilde.isoTop M).hom.hom m)) ∈
      ((tensorOX X M).val.presheaf ⋙ forget _).sections :=
  sorry

/-- The global section associated with m is its pullback from the affine
tilde module on every etale scheme V over X, namely 1 tensor m. -/
noncomputable def tensorOXUnitSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (m : M) : (tensorOX X M).sections :=
  ⟨fun V ↦
    (Scheme.Modules.globalSectionsPullback (etaleToSpecA X V.unop) ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M)).hom
      ((AlgebraicGeometry.tilde.isoTop M).hom.hom m), by exact tensorOXUnitSection_compatible X M m⟩

end AlgebraicGeometry.AlgebraicSpace
