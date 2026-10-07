module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
import StacksCheckRecall

/-!
# Lemma 18.29.2

Compatibility facade for a specified left dual.  The local geometric consequence is owned by
the finite-free retract predicate; comparison with internal Hom is the generic uniqueness of
right adjoints.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (M G : ringedSiteModuleCategory J 𝒪)
variable [p : ExactPairing G M]

/- Lemma 18.29.2 (1) (0FNZ): a module admitting a left dual is locally a finite-free
retract. -/
@[stacks 0FNZ "(1)"]
#check (FiniteFreeRetract.IsLocal.ofExactPairing M G :
  FiniteFreeRetract.IsLocal M)

variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

/- Lemma 18.29.2 (2) (0FNZ): the textbook map from internal Hom to the specified left dual is
the inverse of the canonical right-adjoint-uniqueness isomorphism. -/
@[stacks 0FNZ "(2)"]
#check (p.curryEvaluationIso.symm :
  (ihom M).obj (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≅ G)

/- The forward comparison is the curried evaluation and is therefore inferred as an
isomorphism. -/
#check (CategoryTheory.ExactPairing.isIso_curry_evaluation G M :
  IsIso (MonoidalClosed.curry (ExactPairing.evaluation G M)))

/- Lemma 18.29.2 (3) (0FNZ): evaluation is recovered by uncurrying the forward comparison,
which is the categorical form of the local-section formula in the source. -/
@[stacks 0FNZ "(3)"]
#check (p.uncurry_curryEvaluationIso_hom :
  MonoidalClosed.uncurry p.curryEvaluationIso.hom = p.evaluation')

end SheafOfModules.RingedSite
