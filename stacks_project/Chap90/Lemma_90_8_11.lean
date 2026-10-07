module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Quasi-initiality of versal formal objects

A versal formal object of a predeformation category is weakly initial in the
category of formal objects: every formal object admits a morphism from it.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op [Functor.IsPredeformationCategory p] :
    Functor.IsFibered.InGroupoids p.op :=
  Functor.IsPredeformationCategory.isCofiberedInGroupoids

/-- Lemma 90.8.11: if `p` is a predeformation category and `ξ` is a versal formal
object of `p`, then for every formal object `η` there exists a morphism `ξ ⟶ η`. -/
@[stacks 06HT]
theorem exists_hom_of_isVersal [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] (η : FormalObject p) :
    Nonempty (ξ ⟶ η) :=
  sorry

/-- A based morphism from the restricted coyoneda of a complete local algebra into a
predeformation category is essentially surjective on residue fibres. -/
instance instEssSurj_fiberFunctor_residue {R : CompleteLocalAlgCat Λ k}
    [Functor.IsPredeformationCategory p]
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection R) ⥤ᵇ
      BasedCategory.ofFunctor p) :
    (φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj :=
  sorry

end FormalObject
