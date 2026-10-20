module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences on derived categories

An equivalence between abelian categories is exact in both directions. This file applies the
exact-derived pseudofunctor to its functor, inverse, unit, and counit, producing a canonical
equivalence of unbounded derived categories.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂

namespace CategoryTheory.Equivalence.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The exact functor underlying the forward direction of an equivalence of abelian categories. -/
@[stacks 015F "forward exact functor of an equivalence"]
noncomputable abbrev forwardExact (e : A ≌ B) : A ⥤ₑ B :=
  ExactFunctor.of e.functor

/-- The exact functor underlying the inverse direction of an equivalence of abelian categories. -/
@[stacks 015F "inverse exact functor of an equivalence"]
noncomputable abbrev inverseExact (e : A ≌ B) : B ⥤ₑ A :=
  ExactFunctor.of e.inverse

/-- The functor on derived categories induced by the forward direction of an equivalence. -/
@[stacks 015F "forward derived functor of an equivalence"]
noncomputable abbrev functor (e : A ≌ B) :
    DerivedCategory A ⥤ DerivedCategory B :=
  (forwardExact e).mapDerivedCategory

/-- The functor on derived categories induced by the inverse direction of an equivalence. -/
@[stacks 015F "inverse derived functor of an equivalence"]
noncomputable abbrev inverse (e : A ≌ B) :
    DerivedCategory B ⥤ DerivedCategory A :=
  (inverseExact e).mapDerivedCategory

/-- The exact-functor unit obtained from the unit of an equivalence of abelian categories. -/
@[stacks 015F "exact unit of an equivalence"]
noncomputable abbrev exactUnitIso (e : A ≌ B) :
    ExactFunctor.id A ≅ (forwardExact e).comp (inverseExact e) :=
  ObjectProperty.isoMk (exactFunctor A A) e.unitIso

/-- The exact-functor counit obtained from the counit of an equivalence of abelian categories. -/
@[stacks 015F "exact counit of an equivalence"]
noncomputable abbrev exactCounitIso (e : A ≌ B) :
    (inverseExact e).comp (forwardExact e) ≅ ExactFunctor.id B :=
  ObjectProperty.isoMk (exactFunctor B B) e.counitIso

/-- The derived unit obtained from the identity, natural-transformation, and composition parts of
the exact-derived pseudofunctor. -/
@[stacks 015F "derived unit of an equivalence"]
noncomputable def unitIso (e : A ≌ B) :
    Functor.id (DerivedCategory A) ≅ functor e ⋙ inverse e :=
  ((ExactFunctor.MapDerivedCategory.idFunctorIso A).symm.trans
    (ExactFunctor.MapDerivedCategory.mapIso (exactUnitIso e))).trans
      (ExactFunctor.MapDerivedCategory.compFunctorIso
        (forwardExact e) (inverseExact e))

/-- The derived counit obtained from the composition, natural-transformation, and identity parts
of the exact-derived pseudofunctor. -/
@[stacks 015F "derived counit of an equivalence"]
noncomputable def counitIso (e : A ≌ B) :
    inverse e ⋙ functor e ≅ Functor.id (DerivedCategory B) :=
  ((ExactFunctor.MapDerivedCategory.compFunctorIso
      (inverseExact e) (forwardExact e)).symm.trans
    (ExactFunctor.MapDerivedCategory.mapIso (exactCounitIso e))).trans
      (ExactFunctor.MapDerivedCategory.idFunctorIso B)

/-- The derived unit and counit induced by an equivalence satisfy the triangle identity. -/
@[stacks 015F "triangle identity for a derived equivalence"]
theorem triangle (e : A ≌ B) (K : DerivedCategory A) :
    (functor e).map ((unitIso e).hom.app K) ≫
        (counitIso e).hom.app ((functor e).obj K) =
      𝟙 ((functor e).obj K) := sorry

end CategoryTheory.Equivalence.MapDerivedCategory

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The canonical equivalence of unbounded derived categories induced by an equivalence of
abelian categories. -/
@[stacks 015F "equivalences induce equivalences of derived categories"]
noncomputable def mapDerivedCategory (e : A ≌ B) :
    DerivedCategory A ≌ DerivedCategory B where
  functor := MapDerivedCategory.functor e
  inverse := MapDerivedCategory.inverse e
  unitIso := MapDerivedCategory.unitIso e
  counitIso := MapDerivedCategory.counitIso e
  functor_unitIso_comp := MapDerivedCategory.triangle e

end CategoryTheory.Equivalence
