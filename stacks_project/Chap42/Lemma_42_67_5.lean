module

import StacksCheckRecall
import stacks_project.Chap42.Lemma_42_67_5_Instances
import stacks_project.Chap42.Lemma_42_67_5_ChowPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 42.67.5 (1): the canonical base change of `f` along `g` is flat. -/
@[stacks 0FVK] #check
  (AlgebraicGeometry.Flat.instOverPullbackMap :
    ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : Over S}
      (f : X ⟶ Y) [Flat f.left],
      Flat ((Over.pullback g).map f).left)

/- Lemma 42.67.5 (2): the canonical base change of `f` along `g` has relative
dimension `r`. -/
@[stacks 0FVK] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDimension.instOverPullbackMap :
    ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : Over S}
      (f : X ⟶ Y) (r : ℕ) [Scheme.Hom.RelativeDimension f.left r],
      Scheme.Hom.RelativeDimension ((Over.pullback g).map f).left r)

/- Lemma 42.67.5 (3): dimension-shifted base change commutes with flat pullback
on cycle groups. -/
@[stacks 0FVK] #check
  (AlgebraicGeometry.CycleGroup.baseChangePullback_flatPullback :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (k : ℤ),
      (CycleGroup.reindex (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ')
          (by
            rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
              ← add_assoc k c (r : ℤ)])).comp
            ((CycleGroup.baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
              (CycleGroup.flatPullback δ Y X f r k)) =
        (CycleGroup.flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
            ((Over.pullback g).map f) r (k + c)).comp
          (CycleGroup.baseChangePullback g δ δ' c hcompat X.hom k))

/- Lemma 42.67.5 (4): dimension-shifted base change commutes with flat pullback
on Chow groups. -/
@[stacks 0FVK] #check
  (AlgebraicGeometry.ChowGroup.baseChangePullback_flatPullback :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ X) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (k : ℤ),
      (@ChowGroup.reindex ((Over.pullback g).obj Y).left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj Y).hom
            (LocallyOfFiniteType.instOverPullbackObj g Y) inferInstance)
          (((Over.pullback g).obj Y).hom.relativeDimensionFunction δ') inferInstance
          ((k + (r : ℤ)) + c) ((k + c) + (r : ℤ))
          (by
            rw [add_assoc k (r : ℤ) c, add_comm (r : ℤ) c,
              ← add_assoc k c (r : ℤ)])).toAddMonoidHom.comp
            ((ChowGroup.baseChangePullback g δ δ' c hcompat Y.hom (k + (r : ℤ))).comp
              (ChowGroup.flatPullback δ Y X f r k)) =
        (ChowGroup.flatPullback δ' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
            ((Over.pullback g).map f) r (k + c)).comp
          (ChowGroup.baseChangePullback g δ δ' c hcompat X.hom k))
