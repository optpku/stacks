module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8_Predeformation
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal

/-!
# Versal formal objects imply Schlessinger's (S1)

A predeformation category with a versal formal object satisfies Schlessinger's
condition (S1).
-/

@[expose] public section

open CategoryTheory

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

/-- Lemma 90.13.1: if `p` is a predeformation category and `ξ` is a versal formal
object of `p`, then `p` satisfies Schlessinger's condition (S1). -/
@[stacks 06SY]
theorem hasSchlessingerS1_of_isVersal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    HasSchlessingerS1 p := sorry

end CategoryTheory.Functor
