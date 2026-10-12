/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition.Canonical
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal

@[expose] public section

/-!
# Monoidal compatibility of derived-pushforward composition

The canonical comparison from the derived pushforward of a composite to iterated derived
pushforward intertwines relative cup products as soon as that comparison has been identified as
a monoidal natural transformation. Keeping this coherence premise visible avoids inferring it
from unrelated objectwise tensor isomorphisms.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom.modulePushforwardDerived

-- The coherence premise concerns the same canonical tensorators as cupProduct.
-- Local instance justification (defeq pin): NatTrans.IsMonoidal must use the same adjunction-induced tensorators as cupProduct for f, g and their composite; select the existing laxMonoidal structure locally instead of introducing an independent structure.
attribute [local instance] laxMonoidal

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
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
variable [MonoidalCategory (ModuleDerived.{z} X)]
variable [MonoidalCategory (ModuleDerived.{z} Y)]
variable [MonoidalCategory (ModuleDerived.{z} Z)]
variable [(modulePullbackDerived.{z} f).OplaxMonoidal]
variable [(modulePullbackDerived.{z} g).OplaxMonoidal]
variable [(modulePullbackDerived.{z} (f.comp g)).OplaxMonoidal]

/-- Lemma 21.33.4 (0FPN), reusable form: a monoidal derived-pushforward composition comparison
intertwines the relative cup product for the composite with the iterated relative cup product. -/
@[stacks 0FPN]
theorem cupProduct_compComparison
    (h_comparison : IsIso (modulePullbackDerived.compComparison f g))
    [NatTrans.IsMonoidal (compComparison f g h_comparison)]
    (K L : ModuleDerived.{z} X) :
    cupProduct (f.comp g) K L ≫
        (compComparison f g h_comparison).app (K ⊗ L) =
      ((compComparison f g h_comparison).app K ⊗ₘ
          (compComparison f g h_comparison).app L) ≫
        cupProduct g
          ((modulePushforwardDerived.{z} f).obj K)
          ((modulePushforwardDerived.{z} f).obj L) ≫
        (modulePushforwardDerived.{z} g).map (cupProduct f K L) := sorry

end RingedSite.Hom.modulePushforwardDerived
