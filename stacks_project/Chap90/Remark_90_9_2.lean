module

public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_9_1_Smooth

/-!
# Smoothness of predeformation categories along a smooth morphism

If `φ : U → F` is a smooth morphism of predeformation categories over
`ArtinianLocalAlgCat Λ k`, then `F` is smooth if and only if `U` is smooth.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type w} [Category.{v} F] [Category.{v} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_op {H : Type w} [Category.{v} H]
    {r : H ⥤ ArtinianLocalAlgCat Λ k} [IsPredeformationCategory r] :
    IsFibered.InGroupoids r.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Remark 90.9.2: if `p` and `q` are predeformation categories and
`φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p` is a smooth morphism,
then by Lemma 90.8.8 `φ` is essentially surjective, so by Lemma 90.8.7 the
structure morphism of `p` is smooth if and only if the composite
`φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p)` is smooth, i.e. `p` is
smooth if and only if `q` is smooth. -/
@[stacks 06HQ]
theorem isSmooth_iff_of_smooth [IsPredeformationCategory p] [IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [BasedFunctor.IsSmooth φ] :
    IsSmooth p ↔ IsSmooth q := sorry

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

/-- The composite of a based morphism `φ` with the structure morphism of its target
is the structure morphism of its source. -/
theorem comp_toBase (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) :
    φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p) =
      BasedCategory.toBase (BasedCategory.ofFunctor q) := sorry

/-- The structure morphism of `p` is smooth if and only if its composite with a
smooth morphism `φ` of predeformation categories is smooth. -/
theorem isSmooth_toBase_iff_comp [Functor.IsPredeformationCategory p]
    [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [IsSmooth φ] :
    IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) ↔
      IsSmooth (φ ⋙ BasedCategory.toBase (BasedCategory.ofFunctor p)) := sorry

/-- A smooth morphism of predeformation categories over `ArtinianLocalAlgCat Λ k`
is essentially surjective. -/
instance essSurj_of_isPredeformationCategory [Functor.IsPredeformationCategory p]
    [Functor.IsPredeformationCategory q]
    (φ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor p) [IsSmooth φ] :
    φ.toFunctor.EssSurj := sorry

end CategoryTheory.BasedFunctor
