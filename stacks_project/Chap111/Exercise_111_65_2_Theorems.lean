module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Data.Fin.VecNotation
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Picard
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedEquivariant.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.ProperFlat
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

/- Exercise 111.65.2 (Theorems) (1): morphisms `X ⟶ Spec A` correspond to ring maps
`A ⟶ Γ(X, ⊤)` via the `Γ ⊣ Spec` adjunction. -/
@[stacks 0GYA] #check
  (ΓSpec.adjunction.homEquiv :
    ∀ (X : Scheme.{u}) (R : CommRingCatᵒᵖ),
      (Scheme.Γ.rightOp.obj X ⟶ R) ≃ (X ⟶ Scheme.Spec.obj R))

/- Exercise 111.65.2 (Theorems) (2): on an affine scheme `X`, the cohomology of a
quasi-coherent module `ℱ` vanishes in positive degree. -/
@[stacks 0GYA] #check
  (Scheme.higherCohomology_isZero_of_isAffine :
    ∀ {X : Scheme.{u}} [IsAffine X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ),
      0 < p →
        IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : X.Opens)))

/- Exercise 111.65.2 (Theorems) (3): for a field `k` and `0 < n`, the Picard group of
`P^n_k` is additively equivalent to `ℤ`, with `m` corresponding to `𝒪(m)`; this includes
`Pic(P^1_k)`. -/
@[stacks 0GYA] #check
  (ProjectiveSpace.existsIntAddEquivPicardGroupOfField :
    ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
      ∃ e : ℤ ≃+ (ProjectiveSpace.scheme k n).PicardGroup,
        ∀ m : ℤ, e m = Scheme.Modules.picardClass (ProjectiveSpace.twistingSheaf k n m))

/- Exercise 111.65.2 (Theorems) (4): the fibre-dimension function of a proper flat morphism
of finite presentation is locally constant; this includes proper flat morphisms to a
Noetherian base. -/
@[stacks 0GYA] #check
  (Scheme.Hom.FinitePresentation.isLocallyConstant_fiberDimension :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f], IsLocallyConstant f.fiberDimension)

/- Exercise 111.65.2 (Theorems) (5): `𝔾ₘ`-equivariant quasi-coherent modules on a graded
affine scheme reconstruct from their graded global sections: the equivariant affine-tilde
counit is an isomorphism. -/
@[stacks 0GYA] #check
  (GradedSpec.EquivariantSections.counitIsIso :
    {A : Type u} → [CommRing A] → (𝒜 : ℤ → Submodule ℤ A) → [GradedAlgebra 𝒜] →
      (D : Scheme.QCoh.Equivariant MultiplicativeGroup.group (GradedSpec.action 𝒜)) →
        IsIso (GradedSpec.EquivariantSections.counit 𝒜 D))

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules
open Scheme.Modules.Intersection

/-- Factorwise invertibility of `![𝒪(d), 𝒪(e)]` on `P^2`. -/
instance instInvertible_twistingSheafPair (k : Type u) [Field k] (d e : ℤ) :
    ∀ j : Fin 2, Invertible (![twistingSheaf k 2 d, twistingSheaf k 2 e] j) := sorry

/-- Exercise 111.65.2 (Theorems) (6): Bézout on `P^2_k`: the intersection number of the
twisting sheaves `𝒪(d)` and `𝒪(e)` equals `d * e`. -/
@[stacks 0GYA]
theorem intersectionNumber_twistingSheaves_eq_mul
    {k : Type u} [Field k] (d e : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : (scheme k 2).IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] :
    number k (toSpec k 2) (⊥ : (scheme k 2).IdealSheafData)
      (topologicalKrullDim_bot_eq (scheme k 2) (topologicalKrullDim_scheme_eq k 2))
      ![twistingSheaf k 2 d, twistingSheaf k 2 e] = (d * e : ℚ) := sorry

end AlgebraicGeometry.ProjectiveSpace
