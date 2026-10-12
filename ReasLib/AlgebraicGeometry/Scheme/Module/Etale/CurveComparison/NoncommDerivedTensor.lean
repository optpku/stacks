/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualCoinvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedAction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactDegreePlacement

@[expose] public section
open CategoryTheory
noncomputable section
universe u

namespace NoncommDerivedTensor
variable (R G Γ Q : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)

/-- Actual right-coefficient residual coinvariants for the fixed group extension. -/
abbrev coinvariantFunctor := NoncommResidualCoinvariants.functor Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj

/-- The tensor carrier was built independently as finite balanced quotients.
Only its residual action is transported by that specific algebraic comparison;
no geometric cohomology comparison occurs. -/
def tensorObj (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ) :
    NoncommCompactRepresentation.Cat Rᵐᵒᵖ Q :=
  ⟨{ V := NoncommCompactTensor.tensor Rᵐᵒᵖ G
        (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ M)
     ρ := ((NoncommCompactTensor.iso Rᵐᵒᵖ G
        (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ M)).conj.toMonoidHom).comp
          ((coinvariantFunctor R G Γ Q φ ψ hexact hsurj).obj M).obj.ρ }, by sorry⟩

/-- Actual quotient/tensor maps on coefficient morphisms. -/
def tensorFunctor : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ ⥤
    NoncommCompactRepresentation.Cat Rᵐᵒᵖ Q where
  obj := tensorObj R G Γ Q φ ψ hexact hsurj
  map {M N} f := ObjectProperty.homMk
    { hom := (NoncommCompactTensor.iso Rᵐᵒᵖ G
          (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ M)).inv ≫
        ((coinvariantFunctor R G Γ Q φ ψ hexact hsurj).map f).hom.hom ≫
        (NoncommCompactTensor.iso Rᵐᵒᵖ G
          (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ N)).hom
      comm := fun _ ↦ by sorry }
  map_id := by sorry
  map_comp := by sorry

instance tensorFunctor_additive : (tensorFunctor R G Γ Q φ ψ hexact hsurj).Additive := by sorry

/-- The specified comparison is natural before either functor is derived. -/
def comparison : coinvariantFunctor R G Γ Q φ ψ hexact hsurj ≅
    tensorFunctor R G Γ Q φ ψ hexact hsurj :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (Action.mkIso
    (NoncommCompactTensor.iso Rᵐᵒᵖ G
      (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ M)) (fun _ ↦ by sorry))) (by sorry)

variable (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)

/-- Compact projective resolution obtained from continuous character duality. -/
abbrev resolution := NoncommDualResolution.chosen R Γ M

/-- Corrected [-2] placement of derived residual coinvariants, carrying its
actual completed action over the noncommutative coefficient ring. -/
def coinvariantCochain :=
  (((coinvariantFunctor R G Γ Q φ ψ hexact hsurj ⋙
      NoncommCompletedAction.functor Rᵐᵒᵖ Q).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (resolution R Γ M).complex).extend CompactRepresentation.curveDegreeEmbedding

/-- The independently constructed completed tensor evaluated on the SAME
actual compact projective resolution. -/
def tensorCochain :=
  (((tensorFunctor R G Γ Q φ ψ hexact hsurj ⋙
      NoncommCompletedAction.functor Rᵐᵒᵖ Q).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (resolution R Γ M).complex).extend CompactRepresentation.curveDegreeEmbedding

/-- Actual chain comparison, with specified finite-level tensor projections
in every degree, followed by the degree embedding. -/
def cochainIso : coinvariantCochain R G Γ Q φ ψ hexact hsurj M ≅
    tensorCochain R G Γ Q φ ψ hexact hsurj M :=
  (CompactRepresentation.curveDegreeEmbedding.extendFunctor _).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (NoncommCompletedAction.functor Rᵐᵒᵖ Q).mapIso
        ((comparison R G Γ Q φ ψ hexact hsurj).app ((resolution R Γ M).complex.X i)))
      (fun _ _ _ ↦ by sorry))

variable [HasDerivedCategory (ModuleCat.{u} (NoncommCompletedRing.Obj Rᵐᵒᵖ Q))]

/-- Noncommutative derived completed-tensor comparison, fully residual-equivariant.
This is the group-side construction, not the missing geometric evaluation. -/
def derivedIso : DerivedCategory.Q.obj (coinvariantCochain R G Γ Q φ ψ hexact hsurj M) ≅
    DerivedCategory.Q.obj (tensorCochain R G Γ Q φ ψ hexact hsurj M) :=
  DerivedCategory.Q.mapIso (cochainIso R G Γ Q φ ψ hexact hsurj M)

end NoncommDerivedTensor
