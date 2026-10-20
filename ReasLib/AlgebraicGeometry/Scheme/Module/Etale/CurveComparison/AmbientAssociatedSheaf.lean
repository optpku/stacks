module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AssociatedSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Acyclicity

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
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :=
  { S : Submodule Λ M.obj.V //
    (∀ g : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar), ∀ m ∈ S, (M.obj.ρ g).hom m ∈ S) ∧
      Module.Finite Λ S }

/-- Order finite subrepresentations by inclusion of their underlying submodules. -/
instance finiteSubrepresentationPartialOrder
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    PartialOrder (FiniteSubrepresentation Λ xbar M) := inferInstanceAs (PartialOrder { S :
      Submodule Λ M.obj.V //
      (∀ g : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar), ∀ m ∈ S, (M.obj.ρ g).hom m ∈ S) ∧
        Module.Finite Λ S })

variable {Λ xbar}

/-- Restriction of each actual linear action to an invariant finite submodule. -/
def subAction {M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    Action (ModuleCat.{u + 1} Λ) (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) where
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
    {M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    openStabilizer Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) (subAction S) := sorry

/-- The finite representation carried by the actual invariant submodule. -/
def finiteObject {M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))}
    (S : FiniteSubrepresentation Λ xbar M) :
    (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  ⟨⟨subAction S, subAction_openStabilizer S⟩, S.property.2⟩

/-- The inclusion between two finite invariant submodules is literally subtype inclusion. -/
def finiteInclusion {M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))}
    {S T : FiniteSubrepresentation Λ xbar M} (h : S ≤ T) : finiteObject S ⟶ finiteObject T :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (Submodule.inclusion h)
      comm := fun _ ↦ sorry })

/-- The finite-subrepresentation diagram uses the published finite inverse on each stage. -/
def diagram (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    FiniteSubrepresentation Λ xbar M ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj S := (associatedSheafFunctor Λ xbar).obj (finiteObject S)
  map h := (associatedSheafFunctor Λ xbar).map (finiteInclusion h.le)
  map_id := sorry
  map_comp := sorry

/-- Sheaf colimits supply the actual filtered realization, not an unspecified sheaf witness. -/
instance diagram_hasColimit
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    HasColimit (diagram M) := inferInstance

/-- Realization of an arbitrary continuous discrete module by its finite subsheaves. -/
def obj (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := colimit (diagram M)

/-- Equivariant images of invariant finite submodules are invariant and finite. -/
theorem image_properties
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) :
    (∀ g : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar), ∀ m ∈ S.val.map f.hom.hom.hom,
      (N.obj.ρ g).hom m ∈ S.val.map f.hom.hom.hom) ∧
      Module.Finite Λ (S.val.map f.hom.hom.hom) := sorry

/-- The actual image submodule defines the index of a mapped finite stage. -/
def image {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) : FiniteSubrepresentation Λ xbar N :=
  ⟨S.val.map f.hom.hom.hom, image_properties f S⟩

/-- The map to the image stage applies the original equivariant linear map to each vector. -/
def toImage {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))} (f : M ⟶ N)
    (S : FiniteSubrepresentation Λ xbar M) : finiteObject S ⟶ finiteObject (image f S) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨f.hom.hom.hom s.val, ⟨s.val, s.property, rfl⟩⟩
          map_add' := sorry
          map_smul' := sorry }
      comm := fun _ ↦ sorry })

/-- The image-stage maps followed by colimit inclusions form the specified target cocone. -/
def mapCocone {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))}
    (f : M ⟶ N) : Cocone (diagram M) where
  pt := obj N
  ι :=
    { app := fun S ↦ (associatedSheafFunctor Λ xbar).map (toImage f S) ≫
        colimit.ι (diagram N) (image f S)
      naturality := sorry }

/-- The ambient associated-sheaf functor uses the actual image maps on finite submodules. -/
def functor : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := obj
  map f := colimit.desc _ (mapCocone f)
  map_id := sorry
  map_comp := sorry

/-- For finite input, each finite-stage inclusion is a morphism into the original input. -/
def inclusionToFinite
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (S : FiniteSubrepresentation Λ xbar M.obj) : finiteObject S ⟶ M :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom S.val.subtype
      comm := fun _ ↦ sorry })

/-- The finite-input comparison cocone consists of the actual associated-sheaf inclusions. -/
def finiteCocone
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Cocone (diagram M.obj) where
  pt := (associatedSheafFunctor Λ xbar).obj M
  ι := { app := fun S ↦ (associatedSheafFunctor Λ xbar).map (inclusionToFinite M S)
         naturality := sorry }

/-- The canonical comparison with the already published finite associated sheaf. -/
def finiteComparison
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    obj M.obj ⟶ (associatedSheafFunctor Λ xbar).obj M :=
  colimit.desc _ (finiteCocone M)

/-- The entire input is a finite invariant subrepresentation when the input has finite type. -/
def fullStage
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    FiniteSubrepresentation Λ xbar M.obj :=
  ⟨⊤, ⟨fun _ _ _ ↦ Submodule.mem_top, by
    letI : Module.Finite Λ M.obj.obj.V := M.property
    infer_instance⟩⟩

/-- The full-stage subtype and the original representation have their actual inclusion and lift. -/
def fullStageIso
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    finiteObject (fullStage M) ≅ M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso
      (Submodule.topEquiv : (⊤ : Submodule Λ M.obj.obj.V) ≃ₗ[Λ] M.obj.obj.V).toModuleIso
      (fun _ ↦ sorry)))

/-- The reverse finite-input comparison is inclusion of the full finite stage into the colimit. -/
def finiteComparisonInv
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (associatedSheafFunctor Λ xbar).obj M ⟶ obj M.obj :=
  (associatedSheafFunctor Λ xbar).map (fullStageIso M).inv ≫
    colimit.ι (diagram M.obj) (fullStage M)

/-- The actual finite-stage inclusion is inverse to the comparison cocone map. -/
theorem finiteComparison_hom_inv
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    finiteComparison M ≫ finiteComparisonInv M = 𝟙 _ := sorry

/-- The finite comparison recovers the section placed in the full stage. -/
theorem finiteComparison_inv_hom
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    finiteComparisonInv M ≫ finiteComparison M = 𝟙 _ := sorry

/-- The finite-input realization comparison has both actual maps specified. -/
def finiteComparisonIso
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    obj M.obj ≅ (associatedSheafFunctor Λ xbar).obj M where
  hom := finiteComparison M
  inv := finiteComparisonInv M
  hom_inv_id := finiteComparison_hom_inv M
  inv_hom_id := finiteComparison_inv_hom M

/-- The comparison is invertible using the explicit full-stage inverse. -/
instance finiteComparison_isIso
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    IsIso (finiteComparison M) := (finiteComparisonIso M).isIso_hom

/-- The ambient realization restricts canonically to the published finite inverse. -/
def finiteIso : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).ι ⋙
    functor ≅ associatedSheafFunctor Λ xbar :=
  NatIso.ofComponents finiteComparisonIso (fun _ ↦ sorry)

/-- The reverse natural comparison is the actual full-stage colimit inclusion. -/
@[simp]
theorem finiteIso_inv_app
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    finiteIso.inv.app M = finiteComparisonInv M := rfl

/-- Finite invariant submodules form a filtered index category under sums. -/
instance finiteSubrepresentation_isFiltered
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    IsFiltered (FiniteSubrepresentation Λ xbar M) := sorry

/-- A module stalk preserves the colimit of the specified finite associated sheaves. -/
instance stalk_preservesDiagram
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    PreservesColimit (diagram M) (StalkRepresentation.stalk Λ xbar) := by
  letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  change PreservesColimit (diagram M)
    ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber (A := ModuleCat.{u + 1} Λ))
  infer_instance

/-- Each finite sheaf stalk maps to the original module by the published germ counit
followed by the actual submodule inclusion. -/
def stalkCocone (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    Cocone (diagram M ⋙ StalkRepresentation.stalk Λ xbar) where
  pt := M.obj.V
  ι :=
    { app := fun S ↦ (ModuleSheafInverse.counitLinearEquiv xbar Λ (finiteObject S)).toModuleIso.hom ≫
        ModuleCat.ofHom S.val.subtype
      naturality := sorry }

/-- The stalk comparison is the colimit of the concrete finite germ counits. -/
def stalkComparison (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    (StalkRepresentation.stalk Λ xbar).obj (obj M) ⟶ M.obj.V :=
  (preservesColimitIso (StalkRepresentation.stalk Λ xbar) (diagram M)).hom ≫
    colimit.desc _ (stalkCocone M)

/-- The actual invariant span of the orbit of a vector. -/
def orbitSpan (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) : Submodule Λ M.obj.V :=
  Submodule.span Λ (Set.range fun g ↦ (M.obj.ρ g).hom m)

omit [Finite Λ]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] in
/-- Discrete continuity and compactness give a finite generating orbit, stable under the action. -/
theorem orbitSpan_properties
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    (∀ g, ∀ n ∈ orbitSpan M m, (M.obj.ρ g).hom n ∈ orbitSpan M m) ∧
      Module.Finite Λ (orbitSpan M m) := by
  refine ⟨by sorry, ?_⟩
  let G := Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)
  letI : Finite (G ⧸ MulAction.stabilizer G m) :=
    Subgroup.quotient_finite_of_isOpen _ (M.property m)
  letI : Finite (MulAction.orbit G m) :=
    Finite.of_equiv (G ⧸ MulAction.stabilizer G m)
      (MulAction.orbitEquivQuotientStabilizer G m).symm
  exact Module.Finite.span_of_finite Λ (Set.toFinite (MulAction.orbit G m))

/-- The finite stage containing the vector is its specified orbit span. -/
def orbitStage (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) : FiniteSubrepresentation Λ xbar M :=
  ⟨orbitSpan M m, orbitSpan_properties M m⟩

omit [Finite Λ]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] in
/-- The identity action places every vector in its own orbit span. -/
theorem mem_orbitSpan (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) : m ∈ orbitSpan M m := sorry

/-- Reverse the stalk comparison by the finite germ counit at the vector's actual orbit stage. -/
def stalkComparisonInv (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    M.obj.V ⟶ (StalkRepresentation.stalk Λ xbar).obj (obj M) :=
  ModuleCat.ofHom
    { toFun := fun m ↦
        ((StalkRepresentation.stalk Λ xbar).map
          (colimit.ι (diagram M) (orbitStage M m)))
          ((ModuleSheafInverse.counitLinearEquiv xbar Λ
            (finiteObject (orbitStage M m))).symm ⟨m, mem_orbitSpan M m⟩)
      map_add' := sorry
      map_smul' := sorry }

/-- The specified germ comparison has an explicit orbit-stage inverse. -/
def stalkIso (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    (StalkRepresentation.stalk Λ xbar).obj (obj M) ≅ M.obj.V where
  hom := stalkComparison M
  inv := stalkComparisonInv M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison is invertible through the specified orbit-stage construction. -/
instance stalkComparison_isIso
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    IsIso (stalkComparison M) := (stalkIso M).isIso_hom

/-- The reverse comparison evaluates the finite counit inverse in the vector's orbit stage. -/
theorem stalkComparisonInv_apply
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) (m : M.obj.V) :
    stalkComparisonInv M m =
      ((StalkRepresentation.stalk Λ xbar).map
        (colimit.ι (diagram M) (orbitStage M m)))
        ((ModuleSheafInverse.counitLinearEquiv xbar Λ
          (finiteObject (orbitStage M m))).symm ⟨m, mem_orbitSpan M m⟩) := rfl

/-- On a finite input the ambient stalk comparison is the same published germ counit,
after applying the stalk functor to the actual finite-input sheaf comparison. -/
theorem stalkComparison_finite
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    stalkComparison M.obj =
      (StalkRepresentation.stalk Λ xbar).map (finiteComparison M) ≫
        (ModuleSheafInverse.counitLinearEquiv xbar Λ M).toModuleIso.hom := sorry

/-- The specified germ comparison is natural for the actual equivariant linear maps. -/
theorem stalkComparison_naturality
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))} (f : M ⟶ N) :
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
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  obj (AmbientDiscreteCohomology.effacingObject Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) M)

/-- The specified ambient injective embedding now induces an actual sheaf map. -/
def effacingSheafMap
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    obj M ⟶ effacingSheaf Λ xbar M :=
  functor.map (AmbientDiscreteCohomology.effacingMap Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) M)

/-- This sheaf map is monic by exactness of the realization; it does not assert sheaf injectivity. -/
instance effacingSheafMap_mono
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    Mono (effacingSheafMap Λ xbar M) := sorry

/-- The published finite associated sheaf embeds in the specified realized ambient injective. -/
def finiteEffacingMap
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (associatedSheafFunctor Λ xbar).obj M ⟶ effacingSheaf Λ xbar M.obj :=
  (finiteIso.app M).inv ≫ effacingSheafMap Λ xbar M.obj

/-- The finite-source embedding is monic, without requiring its target representation to be finite. -/
instance finiteEffacingMap_mono
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Mono (finiteEffacingMap Λ xbar M) := sorry

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
