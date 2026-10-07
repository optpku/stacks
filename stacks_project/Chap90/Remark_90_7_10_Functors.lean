module

public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_22_2_TypesCompletion

/-!
# Restriction and completion as 1-functors on Type-valued functors

Precomposition with `ArtinianLocalAlgCat.inclusion` restricts functors
`Ĉ_Λ ⥤ Type w` to `C_Λ ⥤ Type w`. Set-valued completion assembles
`typesCompletion` and `typesCompletionMap` into a 1-functor in the opposite
direction. The canonical quotient maps `R ⟶ inclusion.obj (R.truncation n)`
are the stages of the unit of the resulting adjunction.
-/

@[expose] public section

open CategoryTheory IsLocalRing

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The canonical projection from a complete local algebra to the included `n`th
maximal-adic truncation. -/
def truncationToInclusion (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (R.truncation n) where
  hom := Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `truncationToInclusion` is the quotient map. -/
theorem truncationToInclusion_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationToInclusion R n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)) := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- Restriction of Type-valued functors along `ArtinianLocalAlgCat.inclusion`. -/
def typesRestrictInclusion :
    (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤ (ArtinianLocalAlgCat Λ k ⥤ Type w) :=
  (whiskeringLeft (ArtinianLocalAlgCat Λ k) (CompleteLocalAlgCat Λ k) (Type w)).obj
    ArtinianLocalAlgCat.inclusion

/-- Restriction of a Type-valued functor is precomposition with inclusion. -/
theorem typesRestrictInclusion_obj (G : CompleteLocalAlgCat Λ k ⥤ Type w) :
    typesRestrictInclusion.obj G = ArtinianLocalAlgCat.inclusion ⋙ G := sorry

/-- Restriction acts on natural transformations by left whiskering with inclusion. -/
theorem typesRestrictInclusion_map {G H : CompleteLocalAlgCat Λ k ⥤ Type w} (α : G ⟶ H) :
    typesRestrictInclusion.map α = whiskerLeft ArtinianLocalAlgCat.inclusion α := sorry

/-- The 1-functor sending a Type-valued functor on `C_Λ` to its set-valued completion
on `Ĉ_Λ`. -/
def typesCompletionFunctor :
    (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤ (CompleteLocalAlgCat Λ k ⥤ Type w) where
  obj := typesCompletion
  map := typesCompletionMap
  map_id := typesCompletionMap_id
  map_comp := typesCompletionMap_comp

/-- The object map of `typesCompletionFunctor` is set-valued completion. -/
theorem typesCompletionFunctor_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionFunctor.obj F = typesCompletion F := sorry

/-- The morphism map of `typesCompletionFunctor` is `typesCompletionMap`. -/
theorem typesCompletionFunctor_map {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G) :
    typesCompletionFunctor.map α = typesCompletionMap α := sorry

end CategoryTheory.Functor
