module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.DerivationRestriction
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TangentSpace

/-!
# Tangent spaces of prorepresentable functors

The tangent space of restricted coyoneda identifies with the vector space of
residue-valued derivations of its representing complete local algebra.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The tangent space of restricted coyoneda corresponds to residue-valued derivations. -/
def tangentSpaceEquivDerivation (S : CompleteLocalAlgCat Λ k) :
    tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S) ≃ Derivation Λ S.carrier k :=
  CompleteLocalAlgCat.dualNumberHomEquivDerivation S

/-- The tangent-space correspondence takes the infinitesimal component of a dual-number morphism. -/
theorem tangentSpaceEquivDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :
    tangentSpaceEquivDerivation S f = CompleteLocalAlgCat.dualNumberHomToDerivation S f := rfl

/-- The inverse tangent-space correspondence reconstructs a dual-number morphism. -/
theorem tangentSpaceEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    (tangentSpaceEquivDerivation S).symm D =
      CompleteLocalAlgCat.dualNumberDerivationToHom S D := rfl

/-- The additive group of residue-valued derivations transports to the tangent space. -/
instance instAddCommGroup_tangentSpace_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    AddCommGroup (tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :=
  Equiv.addCommGroup (tangentSpaceEquivDerivation S)

/-- The residue-field module of derivations transports to the tangent space. -/
instance instModule_tangentSpace_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    Module k (tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :=
  Equiv.module k (tangentSpaceEquivDerivation S)

/-- Scalar multiplication on the tangent space is transported from residue-valued derivations. -/
theorem smul_tangentSpace (S : CompleteLocalAlgCat Λ k) (c : k)
    (x : tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) :
    c • x = (tangentSpaceEquivDerivation S).symm (c • tangentSpaceEquivDerivation S x) := rfl

/-- The tangent space of restricted coyoneda identifies linearly with residue-valued derivations. -/
def tangentSpaceLinearEquivDerivation (S : CompleteLocalAlgCat Λ k) :
    tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S) ≃ₗ[k] Derivation Λ S.carrier k :=
  Equiv.linearEquiv k (tangentSpaceEquivDerivation S)

/-- The tangent space of a functor represented by a complete local algebra is finite-dimensional. -/
instance finiteDimensional_tangentSpace_restrictedCoyoneda (S : CompleteLocalAlgCat Λ k) :
    FiniteDimensional k (tangentSpace (CompleteLocalAlgCat.restrictedCoyoneda S)) := sorry

/-- The dual-number component of a restricted coyoneda transformation preserves the
transported addition and residue-field scalar multiplication on tangent spaces. -/
theorem tangentSpaceMap_laws {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    let component : tangentSpace (restrictedCoyoneda S) →
        tangentSpace (restrictedCoyoneda R) :=
      (restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.dualNumber Λ k)
    (∀ x y, component (x + y) = component x + component y) ∧
      (∀ (c : k) x, component (c • x) = c • component x) :=
  sorry

/-- The `k`-linear map of tangent spaces of restricted coyoneda functors induced by a
morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k`, given on underlying functions by the
dual-number component of `restrictedCoyonedaMap f`. -/
def tangentSpaceMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    tangentSpace (restrictedCoyoneda S) →ₗ[k] tangentSpace (restrictedCoyoneda R) where
  toFun := (restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.dualNumber Λ k)
  map_add' := (tangentSpaceMap_laws f).1
  map_smul' := (tangentSpaceMap_laws f).2

/-- The underlying function of `tangentSpaceMap f` is the dual-number component of
`restrictedCoyonedaMap f`. -/
theorem tangentSpaceMap_apply {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (x : tangentSpace (restrictedCoyoneda S)) :
    tangentSpaceMap f x =
      (restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.dualNumber Λ k) x :=
  rfl

/-- Under the canonical tangent-space identifications with residue-valued derivations,
the tangent map induced by a complete local algebra morphism is restriction of derivations. -/
@[stacks 06ST]
theorem tangentSpaceEquivDerivation_map {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (x : tangentSpace (restrictedCoyoneda S)) :
    tangentSpaceEquivDerivation R (tangentSpaceMap f x) =
      Hom.mapDerivation f (tangentSpaceEquivDerivation S x) :=
  sorry

end CategoryTheory.Functor.IsPredeformationFunctor

namespace CompleteLocalAlgCat

/-- Evaluating the square-zero component of `restrictedCoyonedaMap f` as a derivation is
restriction of `homToDerivation S V g` along the underlying algebra map of `f`. -/
theorem homToDerivation_restrictedCoyonedaMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V]
    [Module.Finite k V]
    (g : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V))
    (x : R.carrier) :
    homToDerivation R V
        ((restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.squareZero Λ k V) g) x =
      homToDerivation S V g (f.hom x) :=
  sorry

end CompleteLocalAlgCat
