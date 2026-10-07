module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientAssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommInvariants
public import stacks_project.Chap59.Lemma_59_39_1

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace NoncommAssociatedSections
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Global sections are evaluation on the identity object of the small étale site. -/
def sections : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op (globalEtale X))

/-- The geometric point regarded as a pointing of the identity étale object. -/
def globalPoint : (geometricPointEtalePoint xbar).fiber.obj (globalEtale X) :=
  Over.homMk xbar.hom

/-- The section-to-stalk morphism is the actual germ map at the geometric point. -/
def sectionGerm (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sections Λ).obj F ⟶ (StalkRepresentation.stalk Λ xbar).obj F :=
  (geometricPointEtalePoint xbar).toPresheafFiber (globalEtale X) (globalPoint xbar) F.obj

/-- Sections of the ambient associated sheaf, as a functor on all discrete representations. -/
def realizedSections : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) ⥤
    ModuleCat.{u + 1} Λ :=
  functor ⋙ sections Λ

/-- A global section gives its actual vector by germ evaluation followed by the
colimit of the published finite linear stalk counits. -/
def sectionVector (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    (realizedSections Λ xbar).obj M ⟶ M.obj.V :=
  sectionGerm Λ xbar (obj M) ≫ stalkComparison M

/-- Monodromy fixes the germ of a global section of the realized representation. -/
theorem sectionVector_fixed (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)))
    (s : (realizedSections Λ xbar).obj M) (g : Aut (standardFiniteEtaleFiber xbar)) :
    (M.obj.ρ g).hom ((sectionVector Λ xbar M).hom s) = (sectionVector Λ xbar M).hom s := sorry

/-- The canonical sections-to-invariants map is the germ vector with its fixed-vector proof. -/
def sectionsToInvariants (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    (realizedSections Λ xbar).obj M ⟶
      (NoncommInvariants.functor Λ (Aut (standardFiniteEtaleFiber xbar))).obj M :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(sectionVector Λ xbar M).hom s, sectionVector_fixed Λ xbar M s⟩
      map_add' := sorry
      map_smul' := sorry }

/-- Naturality of the specified germ comparison in equivariant linear coefficient maps. -/
theorem sectionsToInvariants_naturality
    {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))} (f : M ⟶ N) :
    (realizedSections Λ xbar).map f ≫ sectionsToInvariants Λ xbar N =
      sectionsToInvariants Λ xbar M ≫
        (NoncommInvariants.functor Λ (Aut (standardFiniteEtaleFiber xbar))).map f := sorry

/-- The actual natural transformation from realized sections to continuous invariants. -/
def sectionsComparison : realizedSections Λ xbar ⟶
    NoncommInvariants.functor Λ (Aut (standardFiniteEtaleFiber xbar)) where
  app := sectionsToInvariants Λ xbar
  naturality := fun _ _ f ↦ sectionsToInvariants_naturality Λ xbar f

/-- Germ evaluation is bijective onto the invariant vectors of the associated sheaf.
The inverse descends each fixed vector from its finite invariant subrepresentation. -/
instance sectionsToInvariants_isIso
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar))) :
    IsIso (sectionsToInvariants Λ xbar M) := sorry

/-- The sections/invariants natural isomorphism inverts only the specified germ map. -/
def sectionsIso : realizedSections Λ xbar ≅
    NoncommInvariants.functor Λ (Aut (standardFiniteEtaleFiber xbar)) :=
  NatIso.ofComponents (fun M ↦ @asIso _ _ _ _ (sectionsToInvariants Λ xbar M)
    (sectionsToInvariants_isIso Λ xbar M))
    (fun f ↦ sectionsToInvariants_naturality Λ xbar f)

/-- On finite inputs the vector underlying the comparison is exactly the published
finite germ counit after the finite-input realization comparison. -/
theorem sectionVector_finite
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    sectionVector Λ xbar M.obj =
      (sections Λ).map (finiteComparison M) ≫
        sectionGerm Λ xbar ((associatedSheafFunctor Λ xbar).obj M) ≫
        (ModuleSheafInverse.counitLinearEquiv xbar Λ M).toModuleIso.hom := sorry

end NoncommAssociatedSections
