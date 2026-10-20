module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.FiberCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 71.15.2: eventual higher-direct-image stalk vanishing and surjectivity
of the canonical restriction map when an invertible module is ample on a scheme fibre. -/
@[stacks 0D39]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_twist_stalk_isZero_and_surjective_of_isAmple_fiber :
  ∀ {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules]
    (L : X.Modules) [isInvertibleObject L] (F : X.Modules) [F.IsCoherent] (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T)
    [Scheme.Modules.IsAmple (moduleOnScheme f y e L)],
    ∃ d0 : ℕ, ∀ d, d0 ≤ d →
      (∀ p, 0 < p →
          IsZero (RingedSpace.stalkModuleCat
            (higherDirectImageOnScheme f (F ⊗ tensorPower L d) p) y)) ∧
        Function.Surjective
          (ConcreteCategory.hom
            (pushforwardStalkToFiberCohomology f (F ⊗ tensorPower L d) y e)))
