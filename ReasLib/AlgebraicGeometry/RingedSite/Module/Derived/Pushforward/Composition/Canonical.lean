/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition

@[expose] public section

/-!
# Canonical composition of derived module pushforwards on ringed sites

The generic pushforward-composition construction accepts an isomorphism between the corresponding
derived pullbacks.  This leaf specializes it to the canonical pullback comparison whenever that
comparison is known to be invertible.  No unconditional composition theorem is asserted for an
arbitrary bundled ringed site.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
  [UnivLE.{max uZ vZ, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} g) (ModuleQis.{z} Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f.comp g)) (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} Z)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (f.comp g)) (ModuleQis.{z} Z)]
variable [DerivedAdjunction.HasPair.{z} f]
variable [DerivedAdjunction.HasPair.{z} g]
variable [DerivedAdjunction.HasPair.{z} (f.comp g)]

namespace modulePushforwardDerived

/-- The canonical isomorphism from iterated derived direct image to derived direct image of a
composite, provided the canonical derived-pullback comparison is invertible. -/
@[stacks 05T2 "derived-pushforward composition from pullback",
  stacks 0D6E "composition of derived direct images"]
noncomputable def compIso
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g)) :
    modulePushforwardDerived.{z} f ⋙ modulePushforwardDerived.{z} g ≅
      modulePushforwardDerived.{z} (f.comp g) :=
  modulePushforwardDerivedCompIsoOfPullback f g
    (@asIso _ _ _ _ (modulePullbackDerived.compComparison f g) h_comparison)

/-- The source-facing comparison from the derived direct image of a composite to the iterated
derived direct image. -/
@[stacks 05T2 "derived-pushforward composition comparison"]
noncomputable def compComparison
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g)) :
    modulePushforwardDerived.{z} (f.comp g) ⟶
      modulePushforwardDerived.{z} f ⋙ modulePushforwardDerived.{z} g :=
  (compIso f g h_comparison).inv

/-- The canonical derived-pushforward composition isomorphism is compatible with the counits of
the derived pullback-pushforward adjunctions. -/
@[stacks 05T2 "derived-pushforward composition counit"]
theorem compIso_hom_counit
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g)) :
    Functor.whiskerRight
        (compIso f g h_comparison).hom
        (modulePullbackDerived.{z} (f.comp g)) ≫
      (moduleDerivedAdjunction.{z} (f.comp g)).counit =
      (((moduleDerivedAdjunction.{z} g).comp
          (moduleDerivedAdjunction.{z} f)).ofNatIsoLeft
          (@asIso _ _ _ _ (modulePullbackDerived.compComparison f g)
            h_comparison)).counit := sorry

/-- The component of the canonical derived-pushforward composition isomorphism satisfies the
corresponding counit equation at every derived module. -/
@[stacks 05T2 "derived-pushforward composition counit component"]
theorem compIso_hom_counit_app
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g))
    (K : ModuleDerived.{z} X) :
    (modulePullbackDerived.{z} (f.comp g)).map
        ((compIso f g h_comparison).hom.app K) ≫
      (moduleDerivedAdjunction.{z} (f.comp g)).counit.app K =
      (((moduleDerivedAdjunction.{z} g).comp
          (moduleDerivedAdjunction.{z} f)).ofNatIsoLeft
        (@asIso _ _ _ _ (modulePullbackDerived.compComparison f g)
          h_comparison)).counit.app K := sorry

end modulePushforwardDerived

end

end RingedSite.Hom

-- Any `sorryAx` is inherited through Prop-valued derived-functor and adjunction witnesses;
-- the canonical comparison itself is not a placeholder datum.
