/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSections
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientGeometry
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The geometric section action functor is additive on actual coefficient maps. -/
instance geometricSectionsActionFunctor_additive :
    (geometricSectionsActionFunctor Λ X ηbar).Additive := sorry

/-- Relative invariants with their arithmetic quotient action are additive. -/
instance residualInvariantsFunctor_additive : (residualInvariantsFunctor Λ X ηbar).Additive := sorry

/-- Derive the independently constructed geometric section action in ALL
discrete arithmetic representations. This is a relative derived model, not yet
the site-cohomology action obtained by deriving on arithmetic sheaves. -/
def higherGeometricSectionAction (n : ℕ) :=
  (geometricSectionsActionFunctor Λ X ηbar).rightDerived n

/-- Higher relative invariants retain the actual residual action as part of their derived output. -/
def higherResidualInvariants (n : ℕ) := (residualInvariantsFunctor Λ X ηbar).rightDerived n

/-- The higher residual comparison is the derived natural transformation of the
actual degree-zero equivariant section-germ comparison. No higher isomorphism is selected. -/
def higherResidualComparison (n : ℕ) :
    higherGeometricSectionAction Λ X ηbar n ≅ higherResidualInvariants Λ X ηbar n :=
  NatIso.rightDerived (geometricSectionsResidualNatIso Λ X ηbar) n

/-- The higher map is precisely right derivation of the specified equivariant degree-zero map. -/
theorem higherResidualComparison_hom (n : ℕ) :
    (higherResidualComparison Λ X ηbar n).hom =
      NatTrans.rightDerived (geometricSectionsResidualNatIso Λ X ηbar).hom n := rfl

end AlgebraicGeometry.SchemeOverField.AmbientGeometry
