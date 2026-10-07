module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.«90_15_0_1»
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.Example_90_15_3_Quotient

/-!
# Versal formal objects with bijective differential

A predeformation category with a versal formal object whose differential is
bijective satisfies Schlessinger's conditions (S1) and (S2), and has
finite-dimensional tangent space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op [IsPredeformationCategory p] :
    IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 90.15.2 (1): if `p` is a predeformation category and `ξ` is a versal
formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then every cospan in `p` with a surjective second leg completes to a commutative
square whose image is a pullback. -/
@[stacks 06IV]
theorem hasSchlessingerS1_of_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective (p.map f2).hom →
        ∃ (y : F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

/-- Lemma 90.15.2 (2): if `p` is a predeformation category and `ξ` is a versal
formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then `p` satisfies Schlessinger's condition (S2). -/
@[stacks 06IV]
theorem hasSchlessingerS2_of_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    HasSchlessingerS2 p := sorry

/-- Inverse of `FormalObject.differential ξ`, as an equivalence `tangentSpace p ≃
Derivation Λ ξ.base.carrier k` obtained from `FormalObject.BijectiveDifferential`. -/
noncomputable def tangentSpaceEquivDerivation
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :
    tangentSpace p ≃ Derivation Λ ξ.base.carrier k :=
  (Equiv.ofBijective (FormalObject.differential ξ) h).symm

/-- `tangentSpaceEquivDerivation` inverts `FormalObject.differential`. -/
theorem tangentSpaceEquivDerivation_symm_apply
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ)
    (D : Derivation Λ ξ.base.carrier k) :
    (tangentSpaceEquivDerivation ξ h).symm D = FormalObject.differential ξ D := sorry

/-- Additive group structure on `tangentSpace p` transported from
`Derivation Λ ξ.base.carrier k` along `tangentSpaceEquivDerivation`. -/
noncomputable abbrev tangentSpaceAddCommGroup
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :
    AddCommGroup (tangentSpace p) :=
  Equiv.addCommGroup (tangentSpaceEquivDerivation ξ h)

/-- Addition on `tangentSpaceAddCommGroup` is transport of addition of derivations. -/
theorem tangentSpaceAddCommGroup_add
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ)
    (x y : tangentSpace p) :
    (tangentSpaceAddCommGroup ξ h).add x y =
      (tangentSpaceEquivDerivation ξ h).symm
        (tangentSpaceEquivDerivation ξ h x + tangentSpaceEquivDerivation ξ h y) := sorry

/-- `k`-module structure on `tangentSpace p` transported from
`Derivation Λ ξ.base.carrier k` along `tangentSpaceEquivDerivation`, using the same
additive group as `tangentSpaceAddCommGroup`. -/
noncomputable abbrev tangentSpaceModule
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :=
  Equiv.module k (tangentSpaceEquivDerivation ξ h)

/-- Scalar multiplication on `tangentSpaceModule` is transport of the `k`-action on
derivations. -/
theorem tangentSpaceModule_smul
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) (c : k) (x : tangentSpace p) :
    (tangentSpaceModule ξ h).smul c x =
      (tangentSpaceEquivDerivation ξ h).symm (c • tangentSpaceEquivDerivation ξ h x) := sorry

/-- Lemma 90.15.2 (3): if `p` is a predeformation category and `ξ` is a versal
formal object of `p` such that `FormalObject.BijectiveDifferential ξ` holds,
then `tangentSpace p` is finite-dimensional over `k` for the `k`-module structure
transported from `Derivation Λ ξ.base.carrier k`. -/
@[stacks 06IV]
theorem finiteDimensional_tangentSpace_of_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    @FiniteDimensional k (tangentSpace p) inferInstance
      (tangentSpaceAddCommGroup ξ h) (tangentSpaceModule ξ h) := sorry

end CategoryTheory.Functor
