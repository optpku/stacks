/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural tensor comparisons for functors

@stack 08I3

This leaf owns the minimal natural datum expressing that a functor preserves tensor products.  It
does not require unit or associativity coherence, so derived and localization constructions can
reuse an available tensor-bifunctor comparison without manufacturing a monoidal instance.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [MonoidalCategory C] [MonoidalCategory D]

/-- `08I3:` The tensor bifunctor of a monoidal category. -/
@[stacks 08I3 "tensor bifunctor"]
noncomputable abbrev tensorFunctor
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] : C × C ⥤ C :=
  MonoidalCategory.tensor C

/-- `08I3:` The minimal natural tensor comparison carried by a functor. -/
@[stacks 08I3 "natural tensor comparison"]
abbrev TensorComparison (F : C ⥤ D) :=
  tensorFunctor C ⋙ F ≅ Functor.prod F F ⋙ tensorFunctor D

namespace TensorComparison

/-- `08I3:` The tensor comparison carried by a strong monoidal functor, in the colax
orientation. -/
@[stacks 08I3 "tensor comparison from a monoidal functor"]
noncomputable abbrev ofMonoidal (F : C ⥤ D) [F.Monoidal] : TensorComparison F :=
  (Functor.Monoidal.μNatIso F).symm

/-- `08I3:` The tensor comparison carried by an explicit `CoreMonoidal` value. -/
@[stacks 08I3 "core-monoidal tensor comparison"]
noncomputable abbrev ofCoreMonoidal (F : C ⥤ D) (h : F.CoreMonoidal) : TensorComparison F :=
  @ofMonoidal C _ D _ _ _ F h.toMonoidal

/-- `08I3:` Transport a tensor comparison between chosen bifunctor models to the ambient tensor
bifunctors. -/
@[stacks 08I3 "tensor comparison transported from bifunctor models"]
noncomputable def ofBifunctorIso
    (F : C ⥤ D) {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    (T : TC ⋙ F ≅ Functor.prod F F ⋙ TD)
    (eC : TC ≅ tensorFunctor C) (eD : TD ≅ tensorFunctor D) :
    TensorComparison F :=
  Functor.isoWhiskerRight eC.symm F ≪≫ T ≪≫
    Functor.isoWhiskerLeft (Functor.prod F F) eD

/-- `08I3:` The identity functor carries the identity tensor comparison. -/
@[stacks 08I3 "identity tensor comparison"]
noncomputable def id
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] : TensorComparison (𝟭 C) :=
  Iso.refl _

/-- `08I3:` Tensor comparisons compose by whiskering their bifunctor isomorphisms. -/
@[stacks 08I3 "composition of tensor comparisons"]
noncomputable def comp
    {E : Type uE} [Category.{vE} E] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) : TensorComparison (F ⋙ G) :=
  Functor.isoWhiskerRight T G ≪≫
    Functor.isoWhiskerLeft (Functor.prod F F) U

end TensorComparison

end CategoryTheory.Functor
