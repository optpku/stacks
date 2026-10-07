module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_67_7
public import stacks_project.Chap42.Lemma_42_67_8_ChernCap

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/-- The grading shifts from an `i`th Chern-class cap and dimension-shifted base
change agree in either order. -/
theorem baseChangeDegree (k c : ℤ) (i : ℕ) :
    (k - (i : ℤ)) + c = k + c - (i : ℤ) := sorry

/-- Lemma 42.67.8: dimension-shifted flat base change commutes with intersection
by every Chern class of a finite locally free module and its canonical pullback. -/
@[stacks 0FVN]
theorem baseChangePullback
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (i : ℕ) (k : ℤ) :
    (@ChowGroup.reindex ((Over.pullback g).obj X).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj X).hom
          (LocallyOfFiniteType.instOverPullbackObj g X) inferInstance)
        (((Over.pullback g).obj X).hom.relativeDimensionFunction δ') inferInstance
        ((k - (i : ℤ)) + c) (k + c - (i : ℤ)) (baseChangeDegree k c i)).toAddMonoidHom.comp
          ((ChowGroup.baseChangePullback g δ δ' c hcompat X.hom (k - (i : ℤ))).comp
            (componentMap δ X.hom E r i k)) =
      (@componentMap S' ((Over.pullback g).obj X).left inferInstance δ' inferInstance
          ((Over.pullback g).obj X).hom (LocallyOfFiniteType.instOverPullbackObj g X)
          ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj E) r i
          (Scheme.Modules.pullback_isFiniteLocallyFreeOfRank
            (pullback.fst X.hom g) E r) (k + c)).comp
        (ChowGroup.baseChangePullback g δ δ' c hcompat X.hom k) := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap
