module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsClosedImmersion

variable {X Z : RingedSpace.{u}} {i : Z ⟶ X}

/- Lemma 17.13.4 (1) and (2) are the canonical exactness and fully-faithful API. -/
#check @RingedSpace.Hom.ModulePushforward.ClosedImmersion.exact
#check @RingedSpace.Hom.ModulePushforward.ClosedImmersion.fullyFaithful

#check @RingedSpace.IsClosedImmersion.pushforwardHomEquiv

#check @RingedSpace.IsClosedImmersion.pushforwardEssImageEquivalence

#check @RingedSpace.IsClosedImmersion.moduleEquivalence

#check @RingedSpace.IsClosedImmersion.moduleEquivalence.functorCompιIso

#check @RingedSpace.IsClosedImmersion.moduleEquivalence.inverseCompPushforwardIso

/- Lemma 17.13.4 (3) (08KS): an `𝒪_X`-module sheaf lies in the essential image of `pushforward i`
exactly when every local section of the ideal sheaf of the closed immersion acts by zero. -/
@[stacks 08KS "(3), ideal-sheaf formulation"]
#check
  (RingedSpace.IsClosedImmersion.mem_essImage_iff_idealSheaf_smul_eq_zero :
    ∀ {X Z : RingedSpace.{u}} {i : Z ⟶ X} [RingedSpace.IsClosedImmersion i]
      (G : X.Modules),
      (pushforward i).essImage G ↔
        ∀ U : TopologicalSpace.Opens X,
          ∀ s : (RingedSpace.Hom.idealSheaf i).val.obj (op U),
            ∀ m : G.val.obj (op U),
              ((RingedSpace.Hom.idealSheafι i).val.app (op U) s) • m = 0)

end AlgebraicGeometry.RingedSpace.IsClosedImmersion
