module

public import ReasLib.RingTheory.CompleteIntersection.OverField
public import stacks_project.Chap90.Definition_90_9_1_Smooth
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

/-!
# Unobstructed deformation category of a local complete intersection

If `P` is a local complete intersection over the residue field `k`, then the
deformation category `Def_P` of Example 93.8.1 is unobstructed.
-/

@[expose] public section

open CategoryTheory Functor

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]

/-- The slice projection `p_{x0} : Def_P ⥤ C_Λ` of Example 93.8.1. -/
abbrev deformationForget : deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- The slice projection of `Def_P` evaluates an object `(A, Q) → (k, P)` to `A`. -/
theorem deformationForget_obj (x : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj x = x.left.base := sorry

/-- The slice projection `p_{x0} : Def_P ⥤ C_Λ` is cofibered in groupoids. -/
instance instInGroupoids_deformationForget :
    IsFibered.InGroupoids (deformationForget Λ k P).op := sorry

/-- Lemma 93.16.1: in Example 93.8.1, if `P` is a local complete intersection over `k`
in the sense of Algebra, Definition 10.135.1, then `Def_P` is unobstructed. -/
@[stacks 0DZH, instance]
instance instIsUnobstructed_deformationCategory [IsLocalCompleteIntersection k P] :
    Functor.IsUnobstructed (deformationForget Λ k P) := sorry

/-- Infinitesimal lifting along surjections in `C_Λ` for objects of `Def_P` when `P` is
a local complete intersection over `k`. -/
theorem deformationCategory_exists_lift [IsLocalCompleteIntersection k P]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y : ArtinianLocalAlgCat Λ k} {x : deformationCategory Λ k P}
    (α : y ⟶ (deformationForget Λ k P).obj x)
    (hα : (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift f α) :
    ∃ (x' : deformationCategory Λ k P) (β : x' ⟶ x)
      (γ : (deformationForget Λ k P).obj x' ⟶ y),
      (deformationForget Λ k P).IsHomLift f β ∧
        (𝟭 (ArtinianLocalAlgCat Λ k)).IsHomLift (𝟙 B) γ ∧
        γ ≫ α = (deformationForget Λ k P).map β := sorry

end FlatAlgebraCat
