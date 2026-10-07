module

public import stacks_project.Chap62.Lemma_62_11_3
public import stacks_project.Chap62.Lemma_62_13_1_Comp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of composition of families of cycles on fibres

This file records that forming the composite family `α ∘ β` commutes with
base change of `X ⟶ Y ⟶ S` along a morphism `g : S' ⟶ S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The base change of `X ⟶ Y` along `g : S' ⟶ S` is locally of finite type
when `X ⟶ Y` is. -/
instance instLocallyOfFiniteType_overPullbackHom {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (overPullbackHom g p f) := sorry

/-- The two presentations of `X' ⟶ S'` obtained from the base change of
`X ⟶ Y ⟶ S` along `g` agree. -/
theorem overPullbackHom_comp_snd {S S' X Y : Scheme.{u}} (g : S' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) :
    pullback.snd (f ≫ p) g = overPullbackHom g p f ≫ pullback.snd p g := sorry

/-- The identity-triangle fibre map comparing the two presentations of
`X' ⟶ S'`. -/
noncomputable def compBaseChangeFiberMap {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (s' : S') :
    (overPullbackHom g p f ≫ pullback.snd p g).fiber s' ⟶
      (pullback.snd (f ≫ p) g).fiber s' :=
  idTriangleFiberMap (𝟙 _) (overPullbackHom_comp_snd g p f) s'

/-- Lemma 62.13.3: the formation of `α ∘ β` is compatible with base change.
If `g : S' ⟶ S` is a morphism of schemes, `X' ⟶ Y'` is the base change of
`X ⟶ Y` by `g`, `α'` is the base change of `α` along `Y' ⟶ Y`, and `β'` is
the base change of `β` along `S' ⟶ S`, then `α' ∘ β'` is the base change of
`α ∘ β` by `g`. -/
@[stacks 0H6K]
theorem comp_baseChange {S S' X Y : Scheme.{u}} (g : S' ⟶ S) (p : Y ⟶ S)
    (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (s' : S')
    (x' : (overPullbackHom g p f ≫ pullback.snd p g).fiber s') :
    toAlgebraicCycle
        (comp (FiberCycleFamily.baseChange (isPullback_overPullbackHom g p f) α)
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback p g) β))
        s' x' =
      toAlgebraicCycle
        (FiberCycleFamily.baseChange (IsPullback.of_hasPullback (f ≫ p) g)
          (comp α β))
        s' (compBaseChangeFiberMap g p f s' x') := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
