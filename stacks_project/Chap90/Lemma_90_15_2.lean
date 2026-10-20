module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.BijectiveDifferential
import StacksCheckRecall

/-!
# Versal formal objects with bijective differential

A predeformation category with a versal formal object whose differential is
bijective satisfies Schlessinger's conditions (S1) and (S2), and has
finite-dimensional tangent space.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.15.2: a versal formal object with bijective differential implies (S2). -/
@[stacks 06IV] #check (CategoryTheory.Functor.hasSchlessingerS2_of_bijectiveDifferential :
  ∀ [CategoryTheory.Functor.IsPredeformationCategory p] (ξ : FormalObject p)
    [FormalObject.IsVersal ξ], FormalObject.BijectiveDifferential ξ →
      CategoryTheory.Functor.HasSchlessingerS2 p)

#check (CategoryTheory.Functor.hasSchlessingerS1_of_isVersal :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [CategoryTheory.Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ], CategoryTheory.Functor.HasSchlessingerS1 p)

#check (CategoryTheory.Functor.finiteDimensional_tangentSpace_of_bijectiveDifferential :
  ∀ [CategoryTheory.Functor.IsPredeformationCategory p] (ξ : FormalObject p)
    [FormalObject.IsVersal ξ] (h : FormalObject.BijectiveDifferential ξ),
    @FiniteDimensional k (CategoryTheory.Functor.tangentSpace p) inferInstance
      (CategoryTheory.Functor.tangentSpaceAddCommGroup ξ h)
      (CategoryTheory.Functor.tangentSpaceModule ξ h))
