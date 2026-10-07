module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.RightDomain.Equivalence.Computations

/-!
# Projection comparisons for right-domain equivalence transport

This leaf contains the projection-level natural isomorphisms induced by the right-domain
equivalence. It imports component computations but does not own the equivalence data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Forward right-domain equivalence preserves the left projection. -/
noncomputable def DomainChange.Right.equivalence.functorFstIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).functor ⋙ π₁ F G ≅
      π₁ F (E.functor ⋙ G) := Iso.refl _
/-- Inverse right-domain equivalence preserves the left projection. -/
noncomputable def DomainChange.Right.equivalence.inverseFstIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).inverse ⋙ π₁ F (E.functor ⋙ G) ≅
      π₁ F G :=
  Iso.inverseCompIso (DomainChange.Right.equivalence.functorFstIso E F G).symm
/-- Forward right-domain equivalence respects compatible right projections. -/
noncomputable def DomainChange.Right.equivalence.functorSndIso
    {B₀' E₀ : Type*} [Category B₀'] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pB : B₀ ⥤ E₀) (pB' : B₀' ⥤ E₀) (α : E.functor ⋙ pB ≅ pB') :
    (DomainChange.Right.equivalence E F G).functor ⋙ (π₂ F G ⋙ pB) ≅
      π₂ F (E.functor ⋙ G) ⋙ pB' :=
  (Functor.associator (DomainChange.Right.map E.functor F G) (π₂ F G) pB).symm ≪≫
    Functor.associator (π₂ F (E.functor ⋙ G)) E.functor pB ≪≫
      Functor.isoWhiskerLeft (π₂ F (E.functor ⋙ G)) α
/-- Inverse right-domain equivalence respects compatible right projections. -/
noncomputable def DomainChange.Right.equivalence.inverseSndIso
    {B₀' E₀ : Type*} [Category B₀'] [Category E₀]
    (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pB : B₀ ⥤ E₀) (pB' : B₀' ⥤ E₀) (α : E.functor ⋙ pB ≅ pB') :
    (DomainChange.Right.equivalence E F G).inverse ⋙
        (π₂ F (E.functor ⋙ G) ⋙ pB') ≅ π₂ F G ⋙ pB :=
  Iso.inverseCompIso (DomainChange.Right.equivalence.functorSndIso E F G pB pB' α).symm

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
