/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Proposition_64_29_3_AssociatedSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import stacks_project.Chap64.Proposition_64_29_3_AmbientAcyclicity

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Finite invariant submodules of an arbitrary discrete continuous representation. -/
def FiniteSubrepresentation
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :=
  { S : Submodule Λ M.obj.V //
    (∀ g : Aut (standardFiniteEtaleFiber xbar), ∀ m ∈ S, (M.obj.ρ g).hom m ∈ S) ∧
      Module.Finite Λ S }

/-- Order finite subrepresentations by inclusion of their underlying submodules. -/
instance finiteSubrepresentationPartialOrder
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    PartialOrder (FiniteSubrepresentation Λ xbar M) := inferInstanceAs (PartialOrder { S :
      Submodule Λ M.obj.V //
      (∀ g : Aut (standardFiniteEtaleFiber xbar), ∀ m ∈ S, (M.obj.ρ g).hom m ∈ S) ∧
        Module.Finite Λ S })

variable {Λ xbar}

/-- Restriction of each actual linear action to an invariant finite submodule. -/
def subAction {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    Action (ModuleCat.{u + 1} Λ) (Aut (standardFiniteEtaleFiber xbar)) where
  V := ModuleCat.of Λ S.val
  ρ :=
    { toFun := fun g ↦ ModuleCat.ofHom
        { toFun := fun m ↦ ⟨(M.obj.ρ g).hom m.val, S.property.1 g m.val m.property⟩
          map_add' := sorry
          map_smul' := sorry }
      map_one' := sorry
      map_mul' := sorry }

/-- Stabilizers in a subrepresentation are the stabilizers of its underlying vectors. -/
theorem subAction_openStabilizer
    {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    openStabilizer Λ (Aut (standardFiniteEtaleFiber xbar)) (subAction S) := sorry

/-- The finite representation carried by the actual invariant submodule. -/
def finiteObject {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ⟨⟨subAction S, subAction_openStabilizer S⟩, S.property.2⟩

/-- The inclusion between two finite invariant submodules is literally subtype inclusion. -/
def finiteInclusion {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))}
    {S T : FiniteSubrepresentation Λ xbar M} (h : S ≤ T) : finiteObject S ⟶ finiteObject T :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Submodule.inclusion h)
      comm := fun _ ↦ sorry })

/-- The finite-subrepresentation diagram uses the published finite inverse on each stage. -/
def diagram (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    FiniteSubrepresentation Λ xbar M ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj S := (associatedSheafFunctor Λ xbar).obj (finiteObject S)
  map h := (associatedSheafFunctor Λ xbar).map (finiteInclusion h.le)
  map_id := sorry
  map_comp := sorry

/-- Sheaf colimits supply the actual filtered realization, not an unspecified sheaf witness. -/
instance diagram_hasColimit
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    HasColimit (diagram M) := inferInstance

/-- Realization of an arbitrary continuous discrete module by its finite subsheaves. -/
def obj (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := colimit (diagram M)

/-- Equivariant images of invariant finite submodules are invariant and finite. -/
theorem image_properties
    {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) :
    (∀ g : Aut (standardFiniteEtaleFiber xbar), ∀ m ∈ S.val.map f.hom.hom.hom,
      (N.obj.ρ g).hom m ∈ S.val.map f.hom.hom.hom) ∧
      Module.Finite Λ (S.val.map f.hom.hom.hom) := sorry

/-- The actual image submodule defines the index of a mapped finite stage. -/
def image {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) : FiniteSubrepresentation Λ xbar N :=
  ⟨S.val.map f.hom.hom.hom, image_properties f S⟩

/-- The map to the image stage applies the original equivariant linear map to each vector. -/
def toImage {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) : finiteObject S ⟶ finiteObject (image f S) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨f.hom.hom.hom s.val, ⟨s.val, s.property, rfl⟩⟩
          map_add' := sorry
          map_smul' := sorry }
      comm := fun _ ↦ sorry })

/-- The image-stage maps followed by colimit inclusions form the specified target cocone. -/
def mapCocone {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))}
    (f : M ⟶ N) : Cocone (diagram M) where
  pt := obj N
  ι :=
    { app := fun S ↦ (associatedSheafFunctor Λ xbar).map (toImage f S) ≫
        colimit.ι (diagram N) (image f S)
      naturality := sorry }

/-- The ambient associated-sheaf functor uses the actual image maps on finite submodules. -/
def functor : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := obj
  map f := colimit.desc _ (mapCocone f)
  map_id := sorry
  map_comp := sorry

/-- For finite input, each finite-stage inclusion is a morphism into the original input. -/
def inclusionToFinite
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)
    (S : FiniteSubrepresentation Λ xbar M.obj) : finiteObject S ⟶ M :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom S.val.subtype
      comm := fun _ ↦ sorry })

/-- The finite-input comparison cocone consists of the actual associated-sheaf inclusions. -/
def finiteCocone
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Cocone (diagram M.obj) where
  pt := (associatedSheafFunctor Λ xbar).obj M
  ι := { app := fun S ↦ (associatedSheafFunctor Λ xbar).map (inclusionToFinite M S)
         naturality := sorry }

/-- The canonical comparison with the already published finite associated sheaf. -/
def finiteComparison
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    obj M.obj ⟶ (associatedSheafFunctor Λ xbar).obj M :=
  colimit.desc _ (finiteCocone M)

/-- The comparison is invertible because the full submodule is a terminal finite stage. -/
instance finiteComparison_isIso
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    IsIso (finiteComparison M) := sorry

/-- The ambient realization restricts canonically to the published finite inverse. -/
def finiteIso : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).ι ⋙
    functor ≅ associatedSheafFunctor Λ xbar :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (finiteComparison M)
    (finiteComparison_isIso M)) (fun _ ↦ sorry)

/-- Finite invariant submodules form a filtered index category under sums. -/
instance finiteSubrepresentation_isFiltered
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    IsFiltered (FiniteSubrepresentation Λ xbar M) := sorry

/-- A module stalk preserves the colimit of the specified finite associated sheaves. -/
instance stalk_preservesDiagram
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    PreservesColimit (diagram M) (StalkRepresentation.stalk Λ xbar) := sorry

/-- Each finite sheaf stalk maps to the original module by the published germ counit
followed by the actual submodule inclusion. -/
def stalkCocone (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    Cocone (diagram M ⋙ StalkRepresentation.stalk Λ xbar) where
  pt := M.obj.V
  ι :=
    { app := fun S ↦ (ModuleSheafInverse.counitLinearEquiv xbar Λ (finiteObject S)).toModuleIso.hom ≫
        ModuleCat.ofHom S.val.subtype
      naturality := sorry }

/-- The stalk comparison is the colimit of the concrete finite germ counits. -/
def stalkComparison (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    (StalkRepresentation.stalk Λ xbar).obj (obj M) ⟶ M.obj.V :=
  (preservesColimitIso (StalkRepresentation.stalk Λ xbar) (diagram M)).hom ≫
    colimit.desc _ (stalkCocone M)

/-- The actual comparison is an isomorphism: over a finite ring a vector's finite
orbit spans a finite invariant submodule, since the fundamental group is compact. -/
instance stalkComparison_isIso
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    IsIso (stalkComparison M) := sorry

/-- The specified germ comparison identifies the ambient realization's stalk with its input. -/
def stalkIso (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    (StalkRepresentation.stalk Λ xbar).obj (obj M) ≅ M.obj.V :=
  @asIso _ _ _ _ (stalkComparison M) (stalkComparison_isIso M)

/-- On a finite input the ambient stalk comparison is the same published germ counit,
after applying the stalk functor to the actual finite-input sheaf comparison. -/
theorem stalkComparison_finite
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    stalkComparison M.obj =
      (StalkRepresentation.stalk Λ xbar).map (finiteComparison M) ≫
        (ModuleSheafInverse.counitLinearEquiv xbar Λ M).toModuleIso.hom := sorry

/-- The specified germ comparison is natural for the actual equivariant linear maps. -/
theorem stalkComparison_naturality
    {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))} (f : M ⟶ N) :
    (StalkRepresentation.stalk Λ xbar).map (functor.map f) ≫ stalkComparison N =
      stalkComparison M ≫ f.hom.hom := sorry

/-- Ambient realization is additive, through finite-stage linear maps and sheaf colimits. -/
instance functor_additive : (functor (Λ := Λ) (xbar := xbar)).Additive := sorry

/-- Ambient realization preserves finite limits; filtered sheaf colimits commute with them. -/
instance functor_preservesFiniteLimits :
    PreservesFiniteLimits (functor (Λ := Λ) (xbar := xbar)) := sorry

/-- Ambient realization preserves finite colimits through the finite inverse and filtered colimits. -/
instance functor_preservesFiniteColimits :
    PreservesFiniteColimits (functor (Λ := Λ) (xbar := xbar)) := sorry

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The actual sheaf realization of the existing ambient cofree/coreflection injective. -/
def effacingSheaf
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  obj (AmbientDiscreteCohomology.effacingObject Λ (Aut (standardFiniteEtaleFiber xbar)) M)

/-- The specified ambient injective embedding now induces an actual sheaf map. -/
def effacingSheafMap
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    obj M ⟶ effacingSheaf Λ xbar M :=
  functor.map (AmbientDiscreteCohomology.effacingMap Λ (Aut (standardFiniteEtaleFiber xbar)) M)

/-- This sheaf map is monic by exactness of the realization; it does not assert sheaf injectivity. -/
instance effacingSheafMap_mono
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    Mono (effacingSheafMap Λ xbar M) := sorry

/-- The published finite associated sheaf embeds in the specified realized ambient injective. -/
def finiteEffacingMap
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (associatedSheafFunctor Λ xbar).obj M ⟶ effacingSheaf Λ xbar M.obj :=
  (finiteIso.app M).inv ≫ effacingSheafMap Λ xbar M.obj

/-- The finite-source embedding is monic, without requiring its target representation to be finite. -/
instance finiteEffacingMap_mono
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Mono (finiteEffacingMap Λ xbar M) := sorry

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
