module

public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap90.Example_90_15_8_Identity
public import stacks_project.Chap90.Theorem_90_15_5
public import stacks_project.Chap90.«90_3_10_3_Comparison»
import StacksCheckRecall

/-!
# The identity predeformation category as a miniversal example

Reinterpreting Lemma 90.9.5 via Theorem 90.15.5: `F = C_Λ` with the identity functor is a
predeformation category satisfying (S1), (S2) and `T F = 0`, hence condition (3) of
Theorem 90.15.5. A minimal versal formal object `ξ` over some `S` satisfies 90.15.0.2,
`Λ → S` is `m_S`-adic formally smooth, and the cotangent identifications of Lemma 90.9.5
hold for `S`. The `R` of Lemma 90.9.5 therefore carries a minimal versal object, and
uniqueness gives `R ≅ S`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open FormalObject

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 90.15.8 (1): `F = C_Λ` via the identity functor is a predeformation category. -/
@[stacks 06T9] #check Functor.instIsPredeformationCategoryId

/-- Example 90.15.8 (2): `F = C_Λ` via the identity functor satisfies Schlessinger's
condition (S1). -/
@[stacks 06T9]
theorem hasSchlessingerS1_id :
    ∀ {x x1 x2 : ArtinianLocalAlgCat Λ k} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective f2.hom →
        ∃ (y : ArtinianLocalAlgCat Λ k) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧ IsPullback π1 π2 f1 f2 :=
  sorry

/- Example 90.15.8 (3): `F = C_Λ` via the identity functor satisfies Schlessinger's
condition (S2). -/
@[stacks 06T9] #check Functor.instHasSchlessingerS2Id

/-- Example 90.15.8 (4): `T F = 0` for `F = C_Λ` via the identity functor. -/
@[stacks 06T9, instance]
noncomputable instance instUnique_tangentSpace_id :
    Unique (Functor.tangentSpace (𝟭 (ArtinianLocalAlgCat Λ k))) where
  default :=
    Functor.tangentSpace.mk (𝟭 (ArtinianLocalAlgCat Λ k))
      ⟨ArtinianLocalAlgCat.dualNumber Λ k, rfl⟩
  uniq := sorry

/-- `identityDown` satisfies Schlessinger's condition (S2). -/
instance instHasSchlessingerS2_identityDown :
    Functor.HasSchlessingerS2 (ArtinianLocalAlgCat.identityDown Λ k) :=
  sorry

/-- The residue map of an object of `Ĉ_Λ` is surjective. -/
theorem algebraMap_surjective (R : CompleteLocalAlgCat Λ k) :
    Function.Surjective (algebraMap R.carrier k) :=
  sorry

/-- The tangent space of `identityDown` is finite-dimensional over `k`. -/
noncomputable instance instFiniteDimensional_tangentSpace_identityDown :
    FiniteDimensional k (Functor.tangentSpace (ArtinianLocalAlgCat.identityDown Λ k)) :=
  sorry

namespace FormalObject

/-- Example 90.15.8 (5): `identityDown` has a minimal versal formal object satisfying
90.15.0.2. -/
@[stacks 06T9]
theorem exists_isMinimalVersal_identity :
    ∃ ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k),
      IsMinimalVersal ξ ∧ BijectiveDifferentialOnOrbits ξ :=
  sorry

/-- Example 90.15.8 (6): if `ξ` is a versal formal object of `identityDown`, then
`algebraMap Λ ξ.base` is formally smooth in the `m_ξ.base`-adic topology. -/
@[stacks 06T9]
theorem formallySmooth_base_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ] :
    (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic (maximalIdeal ξ.base.carrier) :=
  sorry

/-- Example 90.15.8 (7): 90.15.0.2 for a formal object of `identityDown` makes
`Derivation.compAlgebraMap` bijective. -/
@[stacks 06T9]
theorem bijective_compAlgebraMap_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective fun D : Derivation Λ k k ↦ D.compAlgebraMap ξ.base.carrier :=
  sorry

/-- Example 90.15.8 (8): equivalently, `Ω[S⁄Λ] ⊗[S] k → Ω[k⁄Λ]` is bijective. -/
@[stacks 06T9]
theorem bijective_mapBaseChange_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective (mapBaseChange Λ ξ.base.carrier k) :=
  sorry

/-- Example 90.15.8 (9): after `m`-adic formal smoothness, `H1Cotangent Λ k → m_S / m_S²`
is bijective. -/
@[stacks 06T9]
theorem bijective_toKerCotangent_identity
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ) :
    Function.Bijective
      (toKerCotangent Λ ξ.base.carrier k (algebraMap_surjective ξ.base)) :=
  sorry

end FormalObject

namespace ArtinianLocalAlgCat

/-- Example 90.15.8 (10): an object `R` of `Ĉ_Λ` as in Lemma 90.9.5 carries a minimal
versal formal object of `identityDown` satisfying 90.15.0.2. -/
@[stacks 06T9]
theorem isMinimalVersal_truncationFormalObject (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k)) :
    FormalObject.IsMinimalVersal (truncationFormalObject Λ k R) ∧
      FormalObject.BijectiveDifferentialOnOrbits (truncationFormalObject Λ k R) :=
  sorry

/-- Example 90.15.8 (11): uniqueness of minimal versal objects identifies the Lemma 90.9.5
base `R` with the base of any miniversal `ξ` satisfying 90.15.0.2. -/
@[stacks 06T9]
theorem nonempty_iso_base_identity (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k))
    (ξ : FormalObject (identityDown Λ k)) [FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferentialOnOrbits ξ) :
    Nonempty (R ≅ ξ.base) :=
  sorry

end ArtinianLocalAlgCat
