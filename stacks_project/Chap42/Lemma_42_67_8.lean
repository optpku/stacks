/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.FlatBaseChange

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 42.67.8 -/
@[stacks 0FVN] #check
  (AlgebraicGeometry.ChowGroup.ChernClassCap.baseChangePullback :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : ℕ) (k : ℤ),
    (@ChowGroup.reindex ((Over.pullback g).obj X).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj X).hom
          (LocallyOfFiniteType.instOverPullbackObj g X) inferInstance)
        (((Over.pullback g).obj X).hom.relativeDimensionFunction δ') inferInstance
        ((k - (i : ℤ)) + c) (k + c - (i : ℤ))
        (sub_add_eq_add_sub k (i : ℤ) c)).toAddMonoidHom.comp
          ((AlgebraicGeometry.ChowGroup.baseChangePullback g δ δ' c hcompat X.hom
              (k - (i : ℤ))).comp
            (AlgebraicGeometry.ChowGroup.ChernClassCap.componentMap δ X.hom E r i k)) =
      (@AlgebraicGeometry.ChowGroup.ChernClassCap.componentMap S'
          ((Over.pullback g).obj X).left inferInstance δ' inferInstance
          ((Over.pullback g).obj X).hom (LocallyOfFiniteType.instOverPullbackObj g X)
          ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj E) r i
          (Scheme.Modules.pullback_isFiniteLocallyFreeOfRank
            (pullback.fst X.hom g) E r) (k + c)).comp
        (AlgebraicGeometry.ChowGroup.baseChangePullback g δ δ' c hcompat X.hom k))
