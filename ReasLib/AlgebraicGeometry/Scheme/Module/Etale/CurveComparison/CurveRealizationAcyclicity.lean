/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [ConnectedSpace Y] (ybar : GeometricPoint Y)
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [Y.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Actual site cohomology of the all-discrete associated-sheaf realization. -/
def realizedCohomology (n : ℕ) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber ybar)) ⥤ ModuleCat.{u + 1} Λ :=
  functor ⋙ siteModuleCohomologyModuleFunctor (J := Y.smallEtaleTopology) (A := Λ) n

/-- The degree-zero site-cohomology comparison uses the canonical H-zero/sections
equivalence of the underlying additive sheaf, retaining the specified scalar action. -/
def siteH0SectionsLinearEquiv (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (siteModuleCohomologyModuleFunctor (J := Y.smallEtaleTopology) (A := Λ) 0).obj F ≃ₗ[Λ]
      (sections Λ).obj F where
  __ := Sheaf.H.equiv₀ ((sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
      (MorphismProperty.Over.mkIdTerminal @Etale Y)
  map_smul' := sorry

/-- The canonical H-zero-to-invariants map factors through actual global-section germs. -/
def cohomologyZeroComparison : realizedCohomology Λ ybar 0 ⟶
    AmbientDiscreteCohomology.invariants Λ (Aut (standardFiniteEtaleFiber ybar)) where
  app M := (siteH0SectionsLinearEquiv Λ (obj M)).toModuleIso.hom ≫ sectionsToInvariants Λ ybar M
  naturality := sorry

/-- The degree-zero cohomology isomorphism has the specified H-zero and germ maps. -/
def cohomologyZeroIso : realizedCohomology Λ ybar 0 ≅
    AmbientDiscreteCohomology.invariants Λ (Aut (standardFiniteEtaleFiber ybar)) :=
  NatIso.ofComponents (fun M ↦ (siteH0SectionsLinearEquiv Λ (obj M)).toModuleIso ≪≫
    (sectionsIso Λ ybar).app M) (fun f ↦ (cohomologyZeroComparison Λ ybar).naturality f)

/-- The initial derived-to-geometric comparison is the canonical derived unit
normalization followed by the inverse of the actual H-zero/germ comparison. -/
def derivedZeroComparison :
    AmbientDiscreteCohomology.cohomology Λ (Aut (standardFiniteEtaleFiber ybar)) 0 ≅
      realizedCohomology Λ ybar 0 :=
  AmbientDiscreteCohomology.zeroIso Λ (Aut (standardFiniteEtaleFiber ybar)) ≪≫
    (cohomologyZeroIso Λ ybar).symm

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf

namespace AlgebraicGeometry.SchemeOverField.AmbientCurve
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]
variable [ConnectedSpace (geometricBaseChange X)]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

include hcurve hsmooth hconnected

/-- On precisely the smooth geometrically connected non-P1 curve of Proposition
64.29.3, with coefficient order invertible in the ground field, realized ambient
injectives are acyclic for positive geometric étale cohomology (the K(pi,1) step). -/
theorem realizedInjective_acyclic
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (I : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber ηbar))) [Injective I] (n : ℕ) :
    IsZero ((realizedCohomology Λ ηbar (n + 1)).obj I) := sorry

/-- The existing cofree/coreflection embedding effaces the actual realized
geometric cohomology on the eligible curve, with no arbitrary effacement map. -/
theorem realizedEffacingMap_cohomology
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber ηbar))) (n : ℕ) :
    (realizedCohomology Λ ηbar (n + 1)).map
      (AmbientDiscreteCohomology.effacingMap Λ (Aut (standardFiniteEtaleFiber ηbar)) M) = 0 :=
  (realizedInjective_acyclic Λ X ηbar h_ne_P1 hΛ
    (AmbientDiscreteCohomology.effacingObject Λ (Aut (standardFiniteEtaleFiber ηbar)) M) n).eq_of_tgt _ _

/-- The exhibited ambient monomorphism establishes effaceability of the actual
positive geometric cohomology functor under the source's precise curve hypotheses. -/
theorem realizedCohomology_isEffaceable
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) (n : ℕ) :
    (realizedCohomology Λ ηbar (n + 1)).IsEffaceable :=
  fun M ↦ ⟨AmbientDiscreteCohomology.effacingObject Λ (Aut (standardFiniteEtaleFiber ηbar)) M,
    AmbientDiscreteCohomology.effacingMap Λ (Aut (standardFiniteEtaleFiber ηbar)) M,
    inferInstance, realizedEffacingMap_cohomology Λ X ηbar h_ne_P1 hΛ M n⟩

end AlgebraicGeometry.SchemeOverField.AmbientCurve
