module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Identity.Cotangent
import StacksCheckRecall

/-!
# The identity predeformation category and its miniversal bases

The identity category satisfies Schlessinger's conditions and has zero tangent
space. Its minimal versal bases are the formally smooth complete local algebras
with the canonical cotangent identifications.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.H1Cotangent KaehlerDifferential
open FormalObject

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 90.15.8 -/
@[stacks 06T9] #check (ArtinianLocalAlgCat.nonempty_iso_base_identity :
  ∀ (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k))
    (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [FormalObject.IsMinimalVersal ξ]
    (h : FormalObject.BijectiveDifferentialOnOrbits ξ),
    Nonempty (R ≅ ξ.base))

#check (CategoryTheory.Functor.instIsPredeformationCategoryId :
  Functor.IsPredeformationCategory (𝟭 (ArtinianLocalAlgCat Λ k)))

#check (CategoryTheory.Functor.instHasSchlessingerS1Id :
  Functor.HasSchlessingerS1 (𝟭 (ArtinianLocalAlgCat Λ k)))

#check (CategoryTheory.Functor.HasSchlessingerS1.exists_completion
    (p := 𝟭 (ArtinianLocalAlgCat Λ k)) :
  ∀ {x x1 x2 : ArtinianLocalAlgCat Λ k} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
    Function.Surjective f2.hom →
      ∃ (y : ArtinianLocalAlgCat Λ k) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
        CommSq π1 π2 f1 f2 ∧ IsPullback π1 π2 f1 f2)

#check (CategoryTheory.Functor.instHasSchlessingerS2Id :
  Functor.HasSchlessingerS2 (𝟭 (ArtinianLocalAlgCat Λ k)))

#check (CategoryTheory.Functor.instUnique_tangentSpace_id :
  Unique (Functor.tangentSpace (𝟭 (ArtinianLocalAlgCat Λ k))))

#check (CategoryTheory.Functor.instUnique_tangentSpace_identityDown :
  Unique (Functor.tangentSpace (ArtinianLocalAlgCat.identityDown Λ k)))

#check (ArtinianLocalAlgCat.identityDown Λ k :
  ArtinianLocalAlgCat.identityTotal Λ k ⥤ ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.identityTotal_eq Λ k :
  ArtinianLocalAlgCat.identityTotal Λ k =
    ULiftHom.{u + 1} (ArtinianLocalAlgCat Λ k))

#check (ArtinianLocalAlgCat.identityDown_eq Λ k :
  ArtinianLocalAlgCat.identityDown Λ k = ULiftHom.down)

#check (ArtinianLocalAlgCat.identityDown_obj Λ k :
  ∀ A : ArtinianLocalAlgCat Λ k,
    (ArtinianLocalAlgCat.identityDown Λ k).obj (ULiftHom.objUp A) = A)

#check (ArtinianLocalAlgCat.instIsPredeformationCategory_identityDown Λ k :
  Functor.IsPredeformationCategory (ArtinianLocalAlgCat.identityDown Λ k))

#check (ArtinianLocalAlgCat.instIsFiberedInGroupoids_identityDown_op Λ k :
  Functor.IsFibered.InGroupoids (ArtinianLocalAlgCat.identityDown Λ k).op)

#check (ArtinianLocalAlgCat.instIsSmooth_identityDown Λ k :
  Functor.IsSmooth (ArtinianLocalAlgCat.identityDown Λ k))

#check (ArtinianLocalAlgCat.truncationStage Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    ArtinianLocalAlgCat.identityTotal Λ k)

#check (ArtinianLocalAlgCat.truncationStage_eq Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    ArtinianLocalAlgCat.truncationStage Λ k S n = ULiftHom.objUp (S.truncation n))

#check (ArtinianLocalAlgCat.truncationStageMap Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    ArtinianLocalAlgCat.truncationStage Λ k S (n + 1) ⟶
      ArtinianLocalAlgCat.truncationStage Λ k S n)

#check (ArtinianLocalAlgCat.truncationStageMap_eq Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    ArtinianLocalAlgCat.truncationStageMap Λ k S n =
      (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ ArtinianLocalAlgCat.identityTotal Λ k).map
        (S.truncationMap n))

#check (ArtinianLocalAlgCat.truncationStageMap_isHomLift Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    (ArtinianLocalAlgCat.identityDown Λ k).IsHomLift (S.truncationMap n)
      (ArtinianLocalAlgCat.truncationStageMap Λ k S n))

#check (ArtinianLocalAlgCat.truncationFormalObject Λ k :
  ∀ S : CompleteLocalAlgCat Λ k, FormalObject (ArtinianLocalAlgCat.identityDown Λ k))

#check (ArtinianLocalAlgCat.truncationFormalObject_base Λ k :
  ∀ S : CompleteLocalAlgCat Λ k,
    (ArtinianLocalAlgCat.truncationFormalObject Λ k S).base = S)

#check (ArtinianLocalAlgCat.truncationFormalObject_spec Λ k :
  ∀ (S : CompleteLocalAlgCat Λ k) (n : ℕ),
    (ArtinianLocalAlgCat.identityDown Λ k).obj
        ((ArtinianLocalAlgCat.truncationFormalObject Λ k S).system.family n) = S.truncation n ∧
      (ArtinianLocalAlgCat.identityDown Λ k).IsHomLift (S.truncationMap n)
        ((ArtinianLocalAlgCat.truncationFormalObject Λ k S).system.stepMap n))

#check (ArtinianLocalAlgCat.truncationBasedFunctor Λ k :
  ∀ S : CompleteLocalAlgCat Λ k,
    BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection S) ⥤ᵇ
      BasedCategory.ofFunctor (ArtinianLocalAlgCat.identityDown Λ k))

#check (ArtinianLocalAlgCat.truncationBasedFunctor_eq Λ k :
  ∀ S : CompleteLocalAlgCat Λ k,
    (ArtinianLocalAlgCat.truncationBasedFunctor Λ k S).toFunctor =
      ((ULiftHom.down :
          CompleteLocalAlgCat.identityTotal S ⥤
            (CompleteLocalAlgCat.restrictedCoyoneda S).Elements) ⋙
        CategoryOfElements.π (CompleteLocalAlgCat.restrictedCoyoneda S) ⋙
        (ULiftHom.up : ArtinianLocalAlgCat Λ k ⥤ ArtinianLocalAlgCat.identityTotal Λ k)))

#check (ArtinianLocalAlgCat.truncationBasedFunctor_represents Λ k :
  ∀ S : CompleteLocalAlgCat Λ k,
    FormalObject.Represents (ArtinianLocalAlgCat.truncationFormalObject Λ k S)
      (ArtinianLocalAlgCat.truncationBasedFunctor Λ k S))

#check (ArtinianLocalAlgCat.nonempty_iso_truncationFormalObject Λ k :
  ∀ ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k),
    Nonempty (ξ ≅ ArtinianLocalAlgCat.truncationFormalObject Λ k ξ.base))

#check (CategoryTheory.Functor.instHasSchlessingerS1_identityDown :
  Functor.HasSchlessingerS1 (ArtinianLocalAlgCat.identityDown Λ k))

#check (CategoryTheory.Functor.instHasSchlessingerS2_identityDown :
  Functor.HasSchlessingerS2 (ArtinianLocalAlgCat.identityDown Λ k))

#check (CategoryTheory.Functor.instFiniteDimensional_tangentSpace_identityDown :
  FiniteDimensional k
    ((Functor.fiberIsoClassFunctor (ArtinianLocalAlgCat.identityDown Λ k)).obj
      (ArtinianLocalAlgCat.dualNumber Λ k)))

#check (CompleteLocalAlgCat.algebraMap_surjective :
  ∀ R : CompleteLocalAlgCat Λ k, Function.Surjective (algebraMap R.carrier k))

#check (FormalObject.exists_isMinimalVersal_identity :
  ∃ ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k),
      IsMinimalVersal ξ ∧ BijectiveDifferentialOnOrbits ξ)

#check (FormalObject.formallySmooth_base_identity :
  ∀ (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ],
    (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic (maximalIdeal ξ.base.carrier))

#check (FormalObject.bijective_compAlgebraMap_identity :
  ∀ (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ),
    Function.Bijective fun D : Derivation Λ k k ↦ D.compAlgebraMap ξ.base.carrier)

#check (FormalObject.bijective_mapBaseChange_identity :
  ∀ (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k))
    (h : BijectiveDifferentialOnOrbits ξ),
    Function.Bijective (mapBaseChange Λ ξ.base.carrier k))

#check (FormalObject.bijective_toKerCotangent_identity :
  ∀ (ξ : FormalObject (ArtinianLocalAlgCat.identityDown Λ k)) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ),
    Function.Bijective
      (toKerCotangent Λ ξ.base.carrier k (CompleteLocalAlgCat.algebraMap_surjective ξ.base)))

#check (ArtinianLocalAlgCat.isMinimalVersal_truncationFormalObject :
  ∀ (R : CompleteLocalAlgCat Λ k)
    (h_smooth :
      (algebraMap Λ R.carrier).formally_smooth_for_adic (maximalIdeal R.carrier))
    (h_h1 :
      Function.Bijective (toKerCotangent Λ R.carrier k (CompleteLocalAlgCat.algebraMap_surjective R)))
    (h_omega : Function.Bijective (mapBaseChange Λ R.carrier k)),
    FormalObject.IsMinimalVersal (ArtinianLocalAlgCat.truncationFormalObject Λ k R) ∧
      FormalObject.BijectiveDifferentialOnOrbits (ArtinianLocalAlgCat.truncationFormalObject Λ k R))
