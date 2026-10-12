/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Equivalence.Computations

/-!
# Projection comparisons for left-domain equivalence transport

This leaf contains the projection-level natural isomorphisms induced by the left-domain
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

/-- Forward left-domain equivalence respects compatible left projections. -/
noncomputable def DomainChange.Left.equivalence.functorFstIso
    {A₀' E₀ : Type*} [Category A₀'] [Category E₀]
    (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pA : A₀ ⥤ E₀) (pA' : A₀' ⥤ E₀) (α : E.functor ⋙ pA ≅ pA') :
    (DomainChange.Left.equivalence E F G).functor ⋙ (π₁ F G ⋙ pA) ≅
      π₁ (E.functor ⋙ F) G ⋙ pA' :=
  (Functor.associator (DomainChange.Left.map E.functor F G) (π₁ F G) pA).symm ≪≫
    Functor.associator (π₁ (E.functor ⋙ F) G) E.functor pA ≪≫
      Functor.isoWhiskerLeft (π₁ (E.functor ⋙ F) G) α

/-- Inverse left-domain equivalence respects compatible left projections. -/
noncomputable def DomainChange.Left.equivalence.inverseFstIso
    {A₀' E₀ : Type*} [Category A₀'] [Category E₀]
    (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (pA : A₀ ⥤ E₀) (pA' : A₀' ⥤ E₀) (α : E.functor ⋙ pA ≅ pA') :
    (DomainChange.Left.equivalence E F G).inverse ⋙ (π₁ (E.functor ⋙ F) G ⋙ pA') ≅ π₁ F G ⋙ pA :=
  Iso.inverseCompIso (DomainChange.Left.equivalence.functorFstIso E F G pA pA' α).symm

/-- Forward left-domain equivalence is compatible with the right projection. -/
noncomputable def DomainChange.Left.equivalence.functorSndIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).functor ⋙ π₂ F G ≅ π₂ (E.functor ⋙ F) G := Iso.refl _

/-- Inverse left-domain equivalence is compatible with the right projection. -/
noncomputable def DomainChange.Left.equivalence.inverseSndIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).inverse ⋙ π₂ (E.functor ⋙ F) G ≅ π₂ F G :=
  Iso.inverseCompIso (DomainChange.Left.equivalence.functorSndIso E F G).symm

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
