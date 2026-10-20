module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.InvariantSection
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Global sections are evaluation on the identity object of the small étale site. -/
def sections : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op (AlgebraicGeometry.Scheme.Etale.globalEtale X))

/-- The geometric point regarded as a pointing of the identity étale object. -/
def globalPoint : (AlgebraicGeometry.Scheme.GeometricPoint.toSmallEtalePoint xbar).fiber.obj (AlgebraicGeometry.Scheme.Etale.globalEtale X) :=
  Over.homMk xbar.hom

/-- The section-to-stalk morphism is the actual germ map at the geometric point. -/
def sectionGerm (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sections Λ).obj F ⟶ (StalkRepresentation.stalk Λ xbar).obj F :=
  (AlgebraicGeometry.Scheme.GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber (AlgebraicGeometry.Scheme.Etale.globalEtale X) (globalPoint xbar) F.obj

/-- Sections of the ambient associated sheaf, as a functor on all discrete representations. -/
def realizedSections : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) ⥤
    ModuleCat.{u + 1} Λ :=
  functor ⋙ sections Λ

/-- A global section gives its actual vector by germ evaluation followed by the
colimit of the published finite linear stalk counits. -/
def sectionVector (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    (realizedSections Λ xbar).obj M ⟶ M.obj.V :=
  sectionGerm Λ xbar (obj M) ≫ stalkComparison M

/-- Monodromy fixes the germ of a global section of the realized representation. -/
theorem sectionVector_fixed (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (s : (realizedSections Λ xbar).obj M) (g : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) :
    (M.obj.ρ g).hom ((sectionVector Λ xbar M).hom s) = (sectionVector Λ xbar M).hom s := sorry

/-- The canonical sections-to-invariants map is the germ vector with its fixed-vector proof. -/
def sectionsToInvariants (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    (realizedSections Λ xbar).obj M ⟶
      (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).obj M :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(sectionVector Λ xbar M).hom s, sectionVector_fixed Λ xbar M s⟩
      map_add' := sorry
      map_smul' := sorry }

/-- Naturality of the specified germ comparison in equivariant linear coefficient maps. -/
theorem sectionsToInvariants_naturality
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))} (f : M ⟶ N) :
    (realizedSections Λ xbar).map f ≫ sectionsToInvariants Λ xbar N =
      sectionsToInvariants Λ xbar M ≫
        (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).map f := sorry

/-- The actual natural transformation from realized sections to continuous invariants. -/
def sectionsComparison : realizedSections Λ xbar ⟶
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) where
  app := sectionsToInvariants Λ xbar
  naturality := fun _ _ f ↦ sectionsToInvariants_naturality Λ xbar f

/-- An invariant vector gives a section by its finite cyclic realization and colimit inclusion. -/
def invariantsToSections
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).obj M ⟶
      (realizedSections Λ xbar).obj M :=
  ModuleCat.ofHom
    { toFun := fun m ↦ invariantSection Λ xbar M m.val m.property
      map_add' := sorry
      map_smul' := sorry }

/-- Evaluating the section realized from a fixed vector recovers that invariant vector. -/
theorem invariantsToSections_sectionsToInvariants
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    invariantsToSections Λ xbar M ≫ sectionsToInvariants Λ xbar M = 𝟙 _ := sorry

/-- Finite realization of the germ vector recovers the original section. -/
theorem sectionsToInvariants_invariantsToSections
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    sectionsToInvariants Λ xbar M ≫ invariantsToSections Λ xbar M = 𝟙 _ := sorry

/-- Germ evaluation is invertible by the specified finite-realization section map. -/
instance sectionsToInvariants_isIso
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))) :
    IsIso (sectionsToInvariants Λ xbar M) :=
  ⟨⟨invariantsToSections Λ xbar M, sectionsToInvariants_invariantsToSections Λ xbar M,
    invariantsToSections_sectionsToInvariants Λ xbar M⟩⟩

/-- The sections/invariants comparison stores its germ map and finite-realization reverse. -/
def sectionsIso : realizedSections Λ xbar ≅
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) :=
  NatIso.ofComponents
    (fun M ↦
      { hom := sectionsToInvariants Λ xbar M
        inv := invariantsToSections Λ xbar M
        hom_inv_id := sectionsToInvariants_invariantsToSections Λ xbar M
        inv_hom_id := invariantsToSections_sectionsToInvariants Λ xbar M })
    (fun f ↦ sectionsToInvariants_naturality Λ xbar f)

/-- The inverse comparison acts by the actual finite cyclic realization. -/
@[simp] theorem sectionsIso_inv_app
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).obj M) :
    (sectionsIso Λ xbar).inv.app M m = invariantSection Λ xbar M m.val m.property := rfl

/-- On finite inputs the vector underlying the comparison is exactly the published
finite germ counit after the finite-input realization comparison. -/
theorem sectionVector_finite
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    sectionVector Λ xbar M.obj =
      (sections Λ).map (finiteComparison M) ≫
        sectionGerm Λ xbar ((associatedSheafFunctor Λ xbar).obj M) ≫
        (ModuleSheafInverse.counitLinearEquiv xbar Λ M).toModuleIso.hom := sorry

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
