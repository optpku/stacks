module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Forward
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch

/-!
# Finite-type monodromy over arbitrary coefficient rings

The finite-neighborhood colimit carries a natural linear monodromy action.
For an irreducible geometrically unibranch scheme, its canonical germ map
identifies it with the geometric stalk of a finite-type locally constant sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
variable (xbar : GeometricPoint X)

namespace FiniteTypeMonodromy

/-- Monodromy on the finite-neighborhood fiber of a finite-type locally constant
module sheaf has open stabilizers. -/
theorem representation_openStabilizer
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    openStabilizer Λ (Aut (GeometricPoint.finiteFiber xbar))
      { V := (StalkRepresentation.finiteFiber Λ xbar).obj F.obj.obj
        ρ := StalkRepresentation.finiteRepresentation Λ xbar F.obj.obj } := sorry

include huni in
/-- The canonical map from finite étale germs to the geometric stalk is invertible
for finite-type locally constant modules on a geometrically unibranch scheme. -/
theorem germMap_isIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsIso (StalkRepresentation.germMap Λ xbar F.obj) := sorry

include huni in
/-- The finite-neighborhood fiber of a finite-type locally constant module sheaf
is finitely generated over its coefficient ring. -/
theorem module_finite
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Module.Finite Λ ((StalkRepresentation.finiteFiber Λ xbar).obj F.obj.obj) := sorry

end FiniteTypeMonodromy

/-- A finite-type locally constant module sheaf determines a discrete linear
monodromy representation on its finite-neighborhood germs. -/
def discretePi1ModuleOfFiniteTypeLocallyConstantSheaf
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) :=
  ⟨{ V := (StalkRepresentation.finiteFiber Λ xbar).obj F.obj.obj
     ρ := StalkRepresentation.finiteRepresentation Λ xbar F.obj.obj },
    FiniteTypeMonodromy.representation_openStabilizer Λ xbar F⟩

/-- The monodromy representation of a finite-type locally constant module sheaf
is a finitely generated discrete module. -/
def finitePi1ModuleOfFiniteTypeLocallyConstantSheaf
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  ⟨discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F,
    FiniteTypeMonodromy.module_finite Λ huni xbar F⟩

/-- Sheaf morphisms induce equivariant maps on finite-neighborhood germs,
giving the finite-type monodromy functor over arbitrary coefficient rings. -/
def finiteTypeLocallyConstantModuleToFinitePi1Modules :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory where
  obj := finitePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ huni xbar
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := (StalkRepresentation.finiteFiber Λ xbar).map f.hom.hom
      comm := fun σ ↦ StalkRepresentation.finiteAction_naturality Λ xbar f.hom.hom σ })
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact (StalkRepresentation.finiteFiber Λ xbar).map_id F.obj.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact (StalkRepresentation.finiteFiber Λ xbar).map_comp f.hom.hom g.hom.hom

end AlgebraicGeometry.Scheme
