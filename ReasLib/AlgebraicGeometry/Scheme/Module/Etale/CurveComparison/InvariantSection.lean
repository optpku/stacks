module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientAssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections

/-!
# Realizing an invariant vector as a section

A fixed vector spans a finite invariant subrepresentation. Its constant equivariant map
from the identity finite étale cover gives a section of the finite representing sheaf;
the inclusion of that finite stage gives a section of the ambient associated sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
open scoped FintypeCatDiscrete

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The identity scheme, regarded as a finite étale cover. -/
def identityFiniteEtale : FiniteEtale X :=
  MorphismProperty.Over.mk _ (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- The fixed vector gives a constant equivariant map out of the identity cover's fiber. -/
def finiteFixedActionMap
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (m : M.obj.obj.V) (hm : ∀ g, (M.obj.obj.ρ g).hom m = m) :
    (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).obj (identityFiniteEtale (X := X)) ⟶
      ModuleSheafInverse.moduleSet Λ xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun _ ↦ ModuleSheafInverse.carrierEquiv Λ xbar M m
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro y
        change ModuleSheafInverse.carrierEquiv Λ xbar M m =
          ModuleSheafInverse.carrierEquiv Λ xbar M
            ((M.obj.obj.ρ g).hom
              ((ModuleSheafInverse.carrierEquiv Λ xbar M).symm
                (ModuleSheafInverse.carrierEquiv Λ xbar M m)))
        simp only [Equiv.symm_apply_apply, hm g] }

/-- Galois realization takes the constant equivariant map to an actual finite étale section. -/
def finiteFixedSectionMorphism
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (m : M.obj.obj.V) (hm : ∀ g, (M.obj.obj.ρ g).hom m = m) :
    identityFiniteEtale (X := X) ⟶
      (GeometricPoint.fiberAction xbar).asEquivalence.inverse.obj
        (ModuleSheafInverse.moduleSet Λ xbar M) := by
  letI : (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).IsEquivalence :=
    CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
      (GeometricPoint.finiteFiber xbar)
  let E := (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).asEquivalence
  exact E.unitIso.hom.app (identityFiniteEtale (X := X)) ≫
    E.inverse.map (finiteFixedActionMap Λ xbar M m hm)

/-- The represented finite section enters sheafification through its actual unit. -/
def finiteFixedSection
    (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory)
    (m : M.obj.obj.V) (hm : ∀ g, (M.obj.obj.ρ g).hom m = m) :
    ((associatedSheafFunctor Λ xbar).obj M).obj.obj (op (Etale.globalEtale X)) := by
  letI : (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).IsEquivalence :=
    CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
      (GeometricPoint.finiteFiber xbar)
  let E := (AlgebraicGeometry.Scheme.GeometricPoint.fiberAction xbar).asEquivalence
  let T := (FiniteEtale.toEtale X).obj (E.inverse.obj (ModuleSheafInverse.moduleSet Λ xbar M))
  exact (CategoryTheory.toSheafify X.smallEtaleTopology (uliftYoneda.{u + 1}.obj T)).app
    (op (Etale.globalEtale X))
    (ULift.up ((FiniteEtale.toEtale X).map (finiteFixedSectionMorphism Λ xbar M m hm)))

omit [Finite Λ]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] in
/-- The cyclic span of a fixed vector is invariant under the original action. -/
theorem fixedSpan_stable
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) (hm : ∀ g, (M.obj.ρ g).hom m = m) :
    ∀ g, ∀ x ∈ Submodule.span Λ ({m} : Set M.obj.V),
      (M.obj.ρ g).hom x ∈ Submodule.span Λ ({m} : Set M.obj.V) := sorry

/-- The chosen finite stage is the actual cyclic submodule spanned by the fixed vector. -/
def fixedSpan
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) (hm : ∀ g, (M.obj.ρ g).hom m = m) :
    FiniteSubrepresentation Λ xbar M :=
  ⟨Submodule.span Λ ({m} : Set M.obj.V), fixedSpan_stable Λ xbar M m hm, inferInstance⟩

/-- The generator of the fixed cyclic subrepresentation. -/
def fixedSpanGenerator
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) (hm : ∀ g, (M.obj.ρ g).hom m = m) :
    (finiteObject (fixedSpan Λ xbar M m hm)).obj.obj.V :=
  ⟨m, Submodule.subset_span (Set.mem_singleton m)⟩

/-- The generator stays fixed under the restricted finite action. -/
theorem fixedSpanGenerator_fixed
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) (hm : ∀ g, (M.obj.ρ g).hom m = m) (g) :
    ((finiteObject (fixedSpan Λ xbar M m hm)).obj.obj.ρ g).hom
        (fixedSpanGenerator Λ xbar M m hm) = fixedSpanGenerator Λ xbar M m hm := by
  apply Subtype.ext
  exact hm g

/-- Realize a fixed vector in its finite cyclic stage, then use that stage's colimit inclusion. -/
def invariantSection
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)))
    (m : M.obj.V) (hm : ∀ g, (M.obj.ρ g).hom m = m) :
    (obj M).obj.obj (op (Etale.globalEtale X)) :=
  ((colimit.ι (diagram M) (fixedSpan Λ xbar M m hm)).hom.app (op (Etale.globalEtale X)))
    (finiteFixedSection Λ xbar (finiteObject (fixedSpan Λ xbar M m hm))
      (fixedSpanGenerator Λ xbar M m hm) (fixedSpanGenerator_fixed Λ xbar M m hm))

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
