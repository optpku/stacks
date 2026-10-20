module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.RightDomain.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.QuasiInverse

/-!
# Equivalence induced by right-domain transport

Coherence cells, explicit quasi-inverse data, and the resulting equivalence for precomposition of
the right cospan leg by an equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Left-square coherence for the unit of explicit inverse right-domain change. -/
theorem DomainChange.Right.transformUnitIso.leftCoherence
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (CatCospanTransform.id F (E.functor ⋙ G)).squareLeft.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 A₀)).inv F =
      Functor.whiskerLeft F (Functor.leftUnitor (𝟭 D₀)).inv ≫
        ((DomainChange.Right.transform E.functor F G).comp
          (DomainChange.Right.inverseTransform E F G)).squareLeft.iso.hom := sorry

/-- Right-square coherence for the unit of explicit inverse right-domain change. -/
theorem DomainChange.Right.transformUnitIso.rightCoherence
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (CatCospanTransform.id F (E.functor ⋙ G)).squareRight.iso.hom ≫
        Functor.whiskerRight E.unitIso.hom (E.functor ⋙ G) =
      Functor.whiskerLeft (E.functor ⋙ G)
          (Functor.leftUnitor (𝟭 D₀)).inv ≫
        ((DomainChange.Right.transform E.functor F G).comp
          (DomainChange.Right.inverseTransform E F G)).squareRight.iso.hom := sorry

/-- The unit comparison between the identity and right-domain change followed by its explicit
inverse. -/
noncomputable def DomainChange.Right.transformUnitIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform.id F (E.functor ⋙ G) ≅
      (DomainChange.Right.transform E.functor F G).comp
        (DomainChange.Right.inverseTransform E F G) :=
  CatCospanTransform.mkIso (Functor.leftUnitor (𝟭 A₀)).symm E.unitIso
    (Functor.leftUnitor (𝟭 D₀)).symm
    (DomainChange.Right.transformUnitIso.leftCoherence E F G)
      (DomainChange.Right.transformUnitIso.rightCoherence E F G)

/-- Left-square coherence for the counit of explicit inverse right-domain change. -/
theorem DomainChange.Right.transformCounitIso.leftCoherence
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    ((DomainChange.Right.inverseTransform E F G).comp
        (DomainChange.Right.transform E.functor F G)).squareLeft.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 A₀)).hom F =
      Functor.whiskerLeft F (Functor.leftUnitor (𝟭 D₀)).hom ≫
        (CatCospanTransform.id F G).squareLeft.iso.hom := sorry

/-- Right-square coherence for the counit of explicit inverse right-domain change. -/
theorem DomainChange.Right.transformCounitIso.rightCoherence
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    ((DomainChange.Right.inverseTransform E F G).comp
        (DomainChange.Right.transform E.functor F G)).squareRight.iso.hom ≫
        Functor.whiskerRight E.counitIso.hom G =
      Functor.whiskerLeft G (Functor.leftUnitor (𝟭 D₀)).hom ≫
        (CatCospanTransform.id F G).squareRight.iso.hom := sorry

/-- The counit comparison between inverse right-domain change followed by right-domain change and
the identity target cospan transformation. -/
noncomputable def DomainChange.Right.transformCounitIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.inverseTransform E F G).comp
        (DomainChange.Right.transform E.functor F G) ≅
      CatCospanTransform.id F G :=
  CatCospanTransform.mkIso (Functor.leftUnitor (𝟭 A₀)) E.counitIso
    (Functor.leftUnitor (𝟭 D₀))
    (DomainChange.Right.transformCounitIso.leftCoherence E F G)
      (DomainChange.Right.transformCounitIso.rightCoherence E F G)

/-- Right-domain change along an equivalence with its inverse cospan transformation and
comparison isomorphisms retained explicitly. -/
noncomputable def DomainChange.Right.transformQuasiInverse
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform.QuasiInverse (DomainChange.Right.transform E.functor F G) where
  inverse := DomainChange.Right.inverseTransform E F G
  unitIso := DomainChange.Right.transformUnitIso E F G
  counitIso := DomainChange.Right.transformCounitIso E F G

/-- Explicit quasi-inverse data for right-domain change on categorical pullbacks. -/
noncomputable def DomainChange.Right.quasiInverse
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    Functor.QuasiInverse (DomainChange.Right.map E.functor F G) :=
  (DomainChange.Right.transformQuasiInverse E F G).toMapQuasiInverse

/-- The categorical pullback is invariant under precomposing the right leg with an equivalence of
its domain. -/
noncomputable def DomainChange.Right.equivalence {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) : F ⊡ (E.functor ⋙ G) ≌ F ⊡ G :=
  (DomainChange.Right.quasiInverse E F G).adjointifyUnit

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
