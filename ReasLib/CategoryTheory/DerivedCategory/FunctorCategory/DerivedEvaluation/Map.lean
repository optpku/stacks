module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation

@[expose] public section

/-!
# Maps Between Derived Evaluations

A morphism of indexing objects induces natural transformations between the
corresponding evaluation functors at the cochain and derived levels. The
underived transformation is already `CategoryTheory.evaluation.map`.
@stack 0CQD
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

/-- The cochain-level natural transformation induced by an indexing
morphism. -/
@[stacks 0CQD]
abbrev cochainMap {i j : J} (f : i ⟶ j) :
    cochainFunctor J A i ⟶ cochainFunctor J A j :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex
      ((_root_.CategoryTheory.evaluation J A).map f) (up ℤ))
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)

/-- The natural transformation on derived evaluations obtained by the
canonical localization lift of an indexing morphism. -/
@[stacks 0CQD]
abbrev derivedMap {i j : J} (f : i ⟶ j) :
    functor J A i ⟶ functor J A j :=
  Localization.liftNatTrans
    (DerivedCategory.Q :
      CochainComplex (J ⥤ A) ℤ ⥤ DerivedCategory (J ⥤ A))
    (HomologicalComplex.quasiIso (J ⥤ A) (up ℤ))
    (cochainFunctor J A i) (cochainFunctor J A j)
    (functor J A i) (functor J A j) (cochainMap J A f)

end CategoryTheory.FunctorCategory.DerivedEvaluation
