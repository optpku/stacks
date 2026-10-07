module

public import stacks_project.Chap76.Remark_76_45_1_Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)

universe u

/- Remark 76.45.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
representable algebraic spaces over `S` which is locally of finite type, represented
by `f0 : X0 ⟶ Y0`. Then `f0` is locally of finite type. -/
@[stacks 0CSW] #check
  (locallyOfFiniteType_ofOverMap_iff :
    ∀ {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0),
      LocallyOfFiniteType (ofOverMap f0) ↔
        AlgebraicGeometry.LocallyOfFiniteType f0.left)

/- Remark 76.45.1 (2): If `E` is an object of `D_QCoh(𝒪_X)` for `X = ofOver X0`,
then `E` is the pullback of a unique object `E0` in `D_QCoh(𝒪_{X0})`, see
Lemma 75.4.2. -/
@[stacks 0CSW] #check
  (qcohScheme_unique :
    ∀ {S : Scheme.{u}} (U : Over S) {E : ModuleDerived (ofOver U)},
      derivedQuasiCoherentModuleProperty (ofOver U) E →
        ∃ E0 : Scheme.DerivedQCoh U.left,
          isEpsilonStarPullback U E E0 ∧
            ∀ (E0' : Scheme.DerivedQCoh U.left),
              isEpsilonStarPullback U E E0' →
                ∀ (α : EpsilonStarComparisonIso U E E0)
                  (β : EpsilonStarComparisonIso U E E0'),
                  ∃! e : E0 ≅ E0',
                    (epsilonStar U.left ⋙ SmallEtale.inclusion U.left).map e.hom =
                      α.inv ≫ β.hom)

/- Remark 76.45.1 (3): In this situation the phrase “`E` is `m`-pseudo-coherent
relative to `Y`” means that `E0` is `m`-pseudo-coherent relative to `Y0` as defined
in Section 37.59. -/
@[stacks 0CSW] #check
  (IsMPseudoCoherentOver.ofOver_iff :
    ∀ {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
      [LocallyOfFiniteType (ofOverMap f0)]
      (E : ModuleDerived (ofOver X0))
      (hE : derivedQuasiCoherentModuleProperty (ofOver X0) E) (m : ℤ),
      IsMPseudoCoherentOver.ofOver f0 E hE m ↔
        ∃ E0 : Scheme.DerivedQCoh X0.left,
          isEpsilonStarPullback X0 E E0 ∧
            IsMPseudoCoherentOver.onScheme f0.left E0.obj m)
