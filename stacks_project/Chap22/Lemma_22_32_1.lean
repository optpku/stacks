/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Derived
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w z t

open CategoryTheory
open scoped DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v} [DifferentialGradedCategory.{u, v, w} R C]
variable {E : Type z} [Category.{t} E]
variable (x : C) (L : DifferentialGradedCategory.K R C ⥤ E)
variable (S : MorphismProperty (DifferentialGradedCategory.K R C))
variable [L.IsLocalization S]
variable [DifferentialGradedCategory.Representable.HasUnderlyingDerivedFunctor x S]

/- Lemma 22.32.1 (09LK): if ordinary `RHom(x, -)` is source-defined everywhere after
forgetting the `endomorphismDGA x`-action, the canonical enriched right-derived functor takes
values in derived right modules over `endomorphismDGA x`. -/
@[stacks 09LK]
#check
  (DifferentialGradedCategory.Representable.derivedFunctor x L S :
    E ⥤ DifferentialGradedModule.Derived.Category.{u, w}
      (DifferentialGradedCategory.endomorphismDGA x))

/- The source hypothesis is the everywhere-definedness of the ordinary underlying derived-Hom
functor. -/
#check @DifferentialGradedCategory.Representable.HasUnderlyingDerivedFunctor

/- Forgetting the endomorphism action promotes that hypothesis to enriched definedness without
any local instance installation. -/
#check @DifferentialGradedModule.Derived.rightDerivedEverywhereDefined_of_forget

/- Under the standard triangulated localization hypotheses, the canonical total right-derived
functor is exact. -/
#check @CategoryTheory.Functor.totalRightDerived_isTriangulated

/- After deriving, forgetting the endomorphism action recovers the usual right-derived
representable functor by the canonical uniqueness isomorphism. -/
#check @DifferentialGradedCategory.Representable.derivedForgetIso
