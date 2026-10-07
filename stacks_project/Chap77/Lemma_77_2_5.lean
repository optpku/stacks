module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_27_1_QuasiFinite
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.Definition_77_2_2_Impurity
public import stacks_project.Chap77.Lemma_77_2_3_Impurity
public import stacks_project.Chap77.Lemma_77_2_5_Henselization

/-!
# Equivalent characterizations of impurities above a point

In Situation 77.2.1, existence of an impurity of `F` above `y` over the strict
henselization at a geometric point, the associated-point form of that impurity,
existence of an étale-neighbourhood impurity, and existence of an impurity
quasi-finite at the special point are equivalent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Impurity

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- There exists an impurity of `F` above `y` whose base-change morphism is
`strictHenselizationHomOf N` for some small étale neighbourhood of `ybar`, with
special point `closedPoint N`. -/
def exists_strictHenselization (F : X.Modules) (f : X ⟶ Y) (y : Points Y)
    (ybar : GeometricPoint Y) : Prop :=
  ∃ (N : SmallEtaleNeighborhood ybar)
    (y' : (SchemeOver.mk (strictHenselizationHomOf N)).left.left)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
    IsImpurity f F y (SchemeOver.mk (strictHenselizationHomOf N)) y'
      (closedPoint N) ξ

/-- Unfolding of `exists_strictHenselization`. -/
theorem exists_strictHenselization_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y)
    (ybar : GeometricPoint Y) :
    exists_strictHenselization F f y ybar ↔
      ∃ (N : SmallEtaleNeighborhood ybar)
        (y' : (SchemeOver.mk (strictHenselizationHomOf N)).left.left)
        (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
        IsImpurity f F y (SchemeOver.mk (strictHenselizationHomOf N)) y'
          (closedPoint N) ξ :=
  sorry

/-- There exists a relative associated point of the pullback of `F` to `X^{sh}`
that does not specialize into the closed fibre over `closedPoint N`. -/
def exists_relativeAssassin_not_specializes_closedFiber (F : X.Modules)
    (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y) : Prop :=
  ∃ (N : SmallEtaleNeighborhood ybar)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
    ξ ∈ relativeAssassin (Limits.pullback.snd f (strictHenselizationHomOf N))
        (pullbackModules F f N) ∧
      ¬ ∃ θ : Points (Limits.pullback f (strictHenselizationHomOf N)),
          Specializes ξ θ ∧ θ ∈ closedFiber f N

/-- Unfolding of `exists_relativeAssassin_not_specializes_closedFiber`. -/
theorem exists_relativeAssassin_not_specializes_closedFiber_iff (F : X.Modules)
    (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y) :
    exists_relativeAssassin_not_specializes_closedFiber F f y ybar ↔
      ∃ (N : SmallEtaleNeighborhood ybar)
        (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))),
        ξ ∈ relativeAssassin (Limits.pullback.snd f (strictHenselizationHomOf N))
            (pullbackModules F f N) ∧
          ¬ ∃ θ : Points (Limits.pullback f (strictHenselizationHomOf N)),
              Specializes ξ θ ∧ θ ∈ closedFiber f N :=
  sorry

/-- There exists an impurity of `F` above `y` whose base-change morphism is étale. -/
def exists_etaleNeighbourhood (F : X.Modules) (f : X ⟶ Y) (y : Points Y) : Prop :=
  ∃ I : Impurity F f y, AlgebraicSpace.Etale I.g

/-- Unfolding of `exists_etaleNeighbourhood`. -/
theorem exists_etaleNeighbourhood_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y) :
    exists_etaleNeighbourhood F f y ↔
      ∃ I : Impurity F f y, AlgebraicSpace.Etale I.g :=
  sorry

/-- There exists an impurity of `F` above `y` that is quasi-finite at the special
point. -/
def exists_quasiFiniteAt (F : X.Modules) (f : X ⟶ Y) (y : Points Y) : Prop :=
  ∃ I : Impurity F f y,
    FiniteType.QuasiFiniteAt I.g (ofOver.pointsEquiv I.T I.specialPoint)

/-- Unfolding of `exists_quasiFiniteAt`. -/
theorem exists_quasiFiniteAt_iff (F : X.Modules) (f : X ⟶ Y) (y : Points Y) :
    exists_quasiFiniteAt F f y ↔
      ∃ I : Impurity F f y,
        FiniteType.QuasiFiniteAt I.g (ofOver.pointsEquiv I.T I.specialPoint) :=
  sorry

/-- Lemma 77.2.5: in Situation 77.2.1, let `ybar` be a geometric point lying over
`y`. Let `O = etaleLocalRing Y ybar` be the étale local ring of `Y` at `ybar`,
write `Y^{sh} = strictHenselizationScheme ybar = Spec(O)`, `X^{sh}` for the
pullback of `X` along `Y^{sh} ⟶ Y`, and `F^{sh}` for the pullback of `F` to
`X^{sh}`. The following are equivalent: (1) `F` has an impurity
`(Y^{sh} ⟶ Y, y' ⤳ ybar, ξ)` above `y`; (2) some point of
`Ass_{X^{sh}/Y^{sh}}(F^{sh})` does not specialize into the closed fibre
`X_{ybar}` (the associated-point form of an impurity over `Y^{sh}`); (3) `F`
has an impurity above `y` whose pointed base change is an étale neighbourhood
of `(Y, y)`; (4) `F` has an impurity above `y` that is quasi-finite at the
special point. -/
@[stacks 0CVB]
theorem existence_tfae (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.liesOver y) :
    List.TFAE
      [exists_strictHenselization F f y ybar,
        exists_relativeAssassin_not_specializes_closedFiber F f y ybar,
        exists_etaleNeighbourhood F f y, exists_quasiFiniteAt F f y] :=
  sorry

/-- In Situation 77.2.1, an impurity over a strict henselization at `ybar` exists
if and only if some relative associated point of `F^{sh}` fails to specialize
into the closed fibre. -/
theorem exists_strictHenselization_iff_exists_relativeAssassin_not_specializes_closedFiber
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.liesOver y) :
    exists_strictHenselization F f y ybar ↔
      exists_relativeAssassin_not_specializes_closedFiber F f y ybar :=
  sorry

/-- In Situation 77.2.1, an impurity over a strict henselization at `ybar` exists
if and only if an étale-neighbourhood impurity above `y` exists. -/
theorem exists_strictHenselization_iff_exists_etaleNeighbourhood (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : Points Y) (ybar : GeometricPoint Y) (hy : ybar.liesOver y) :
    exists_strictHenselization F f y ybar ↔ exists_etaleNeighbourhood F f y :=
  sorry

/-- In Situation 77.2.1, an étale-neighbourhood impurity above `y` exists if and
only if an impurity quasi-finite at its special point exists. -/
theorem exists_etaleNeighbourhood_iff_exists_quasiFiniteAt (F : X.Modules)
    (f : X ⟶ Y) [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType]
    (y : Points Y) :
    exists_etaleNeighbourhood F f y ↔ exists_quasiFiniteAt F f y :=
  sorry

end Impurity
end AlgebraicGeometry.AlgebraicSpace.Modules
