module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Deformation.Cogroupoid
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRingAtPoint
import Mathlib.Tactic.CrossRefAttribute

/-! # Local-ring dimension from a versal cogroupoid presentation -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open AlgebraicGeometry.GroupoidsOver.Predeformation
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a finite-type field-valued point of an algebraic stack locally of finite
type over a locally Noetherian scheme, a compatible versal complete-local
cogroupoid presentation computes the local-ring dimension as twice the Krull
dimension of the object algebra minus the Krull dimension of the arrow algebra. -/
@[stacks 0DSB]
theorem localRingDimAt_eq_cogroupoid {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    [IsLocallyNoetherian X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom)
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t)
    (h : IsPredeformationCogroupoid x0 openImmersion h_factor ξ B s t c)
    (hx : IsFiniteTypePoint (Points.mk x0)) :
    localRingDimAt (Points.mk x0) hx =
      dimensionDiff (ringKrullDim ξ.base.carrier + ringKrullDim ξ.base.carrier)
        (ringKrullDim B.carrier) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
