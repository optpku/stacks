/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.QuasiInverse

/-!
# Equivalence induced by left-domain transport

Coherence cells, explicit quasi-inverse data, and the resulting equivalence for precomposition of
the left cospan leg by an equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Left-square coherence for the unit of explicit inverse left-domain change. -/
theorem DomainChange.Left.transformUnitIso.leftCoherence
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (CatCospanTransform.id (E.functor ⋙ F) G).squareLeft.iso.hom ≫
        Functor.whiskerRight E.unitIso.hom (E.functor ⋙ F) =
      Functor.whiskerLeft (E.functor ⋙ F)
          (Functor.leftUnitor (𝟭 D₀)).inv ≫
        ((DomainChange.Left.transform E.functor F G).comp
          (DomainChange.Left.inverseTransform E F G)).squareLeft.iso.hom := sorry

/-- Right-square coherence for the unit of explicit inverse left-domain change. -/
theorem DomainChange.Left.transformUnitIso.rightCoherence
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (CatCospanTransform.id (E.functor ⋙ F) G).squareRight.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 B₀)).inv G =
      Functor.whiskerLeft G (Functor.leftUnitor (𝟭 D₀)).inv ≫
        ((DomainChange.Left.transform E.functor F G).comp
          (DomainChange.Left.inverseTransform E F G)).squareRight.iso.hom := sorry

/-- The unit comparison between the identity and left-domain change followed by its explicit
inverse. -/
noncomputable def DomainChange.Left.transformUnitIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform.id (E.functor ⋙ F) G ≅
      (DomainChange.Left.transform E.functor F G).comp
        (DomainChange.Left.inverseTransform E F G) :=
  CatCospanTransform.mkIso E.unitIso (Functor.leftUnitor (𝟭 B₀)).symm
    (Functor.leftUnitor (𝟭 D₀)).symm
    (DomainChange.Left.transformUnitIso.leftCoherence E F G)
      (DomainChange.Left.transformUnitIso.rightCoherence E F G)

/-- Left-square coherence for the counit of explicit inverse left-domain change. -/
theorem DomainChange.Left.transformCounitIso.leftCoherence
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    ((DomainChange.Left.inverseTransform E F G).comp
        (DomainChange.Left.transform E.functor F G)).squareLeft.iso.hom ≫
        Functor.whiskerRight E.counitIso.hom F =
      Functor.whiskerLeft F (Functor.leftUnitor (𝟭 D₀)).hom ≫
        (CatCospanTransform.id F G).squareLeft.iso.hom := sorry

/-- Right-square coherence for the counit of explicit inverse left-domain change. -/
theorem DomainChange.Left.transformCounitIso.rightCoherence
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    ((DomainChange.Left.inverseTransform E F G).comp
        (DomainChange.Left.transform E.functor F G)).squareRight.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 B₀)).hom G =
      Functor.whiskerLeft G (Functor.leftUnitor (𝟭 D₀)).hom ≫
        (CatCospanTransform.id F G).squareRight.iso.hom := sorry

/-- The counit comparison between inverse left-domain change followed by left-domain change and
the identity target cospan transformation. -/
noncomputable def DomainChange.Left.transformCounitIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.inverseTransform E F G).comp
        (DomainChange.Left.transform E.functor F G) ≅
      CatCospanTransform.id F G :=
  CatCospanTransform.mkIso E.counitIso (Functor.leftUnitor (𝟭 B₀))
    (Functor.leftUnitor (𝟭 D₀))
    (DomainChange.Left.transformCounitIso.leftCoherence E F G)
      (DomainChange.Left.transformCounitIso.rightCoherence E F G)

/-- Left-domain change along an equivalence with its inverse cospan transformation and comparison
isomorphisms retained explicitly. -/
noncomputable def DomainChange.Left.transformQuasiInverse
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform.QuasiInverse (DomainChange.Left.transform E.functor F G) where
  inverse := DomainChange.Left.inverseTransform E F G
  unitIso := DomainChange.Left.transformUnitIso E F G
  counitIso := DomainChange.Left.transformCounitIso E F G

/-- Explicit quasi-inverse data for left-domain change on categorical pullbacks. -/
noncomputable def DomainChange.Left.quasiInverse
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    Functor.QuasiInverse (DomainChange.Left.map E.functor F G) :=
  (DomainChange.Left.transformQuasiInverse E F G).toMapQuasiInverse

/-- The categorical pullback is invariant under precomposing the left leg with an equivalence of
its domain. -/
noncomputable def DomainChange.Left.equivalence {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) : (E.functor ⋙ F) ⊡ G ≌ F ⊡ G :=
  (DomainChange.Left.quasiInverse E F G).adjointifyUnit

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
