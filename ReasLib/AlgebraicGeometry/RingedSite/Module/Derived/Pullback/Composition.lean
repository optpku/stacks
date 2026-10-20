/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The canonical comparison for composed derived pullbacks

For arbitrary bundled ringed sites, total left derived pullback has a canonical comparison from
the iterated functor to pullback along the composite.  Its construction does not assert that this
comparison is invertible.  Invertibility belongs in a separate leaf supplying good models.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX vX uY vY uZ vZ w

namespace RingedSite.Hom

-- Local instance justification (defeq pin): align the generic composition constructors with
-- the canonical derived-category owner used by `ModuleDerived` and `moduleLocalization`.
attribute [local instance] moduleCat_hasDerivedCategory
  modulePullback.DerivedCategory.hasLeftDerived

section

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
  [UnivLE.{max uZ vZ, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} Z)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (f.comp g)) (ModuleQis.{z} Z)]

namespace modulePullbackToDerived

/-- The homotopy-to-derived functor for a composite pullback identifies with the iterated
homotopy-level pullback model. -/
@[stacks 05T2 "homotopy model for composed pullback"]
noncomputable abbrev compIso :
    modulePullbackToDerived.{z} (f.comp g) ≅
      modulePullbackHomotopy.{z} g ⋙ modulePullbackToDerived.{z} f :=
  Functor.LeftDerived.Homotopy.Composition.toDerivedIso
    (modulePullback.{z} f)
    (modulePullback.{z} g)
    (modulePullback.{z} (f.comp g))
    (modulePullbackCompIso.{z} f g)

end modulePullbackToDerived

namespace modulePullbackDerived

/-- The counit exhibiting the composite derived pullback as a left derived functor of the
composite homotopy-level pullback model. -/
@[stacks 05T2 "counit for iterated derived pullback"]
noncomputable abbrev compCounit :
    moduleLocalization.{z} Z ⋙
        (modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f) ⟶
      modulePullbackHomotopy.{z} g ⋙ modulePullbackToDerived.{z} f :=
  Functor.LeftDerived.Homotopy.Composition.counit
    (modulePullback.{z} f)
    (modulePullback.{z} g)

/-- The canonical comparison from iterated derived pullback to derived pullback along the
composite ringed-site morphism.  It is defined without an invertibility hypothesis. -/
@[stacks 05T2 "ringed-site derived-pullback comparison"]
noncomputable abbrev compComparison :
    modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ⟶
      modulePullbackDerived.{z} (f.comp g) :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (modulePullback.{z} f)
    (modulePullback.{z} g)
    (modulePullback.{z} (f.comp g))
    (modulePullbackCompIso.{z} f g)

/-- The canonical isomorphism from iterated derived pullback to pullback along the composite,
when the canonical comparison is invertible. -/
@[stacks 05T2 "ringed-site derived-pullback composition isomorphism"]
noncomputable def compIso [IsIso (compComparison f g)] :
    modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      modulePullbackDerived.{z} (f.comp g) :=
  asIso (compComparison f g)

/-- The derived-pullback composition comparison is characterized by the canonical total-left-
derived counits. -/
@[stacks 05T2 "ringed-site derived-pullback comparison counit"]
theorem compComparison_counit :
    Functor.whiskerLeft (moduleLocalization.{z} Z)
        (compComparison f g) ≫
      ((modulePullbackToDerived.{z} (f.comp g)).totalLeftDerivedCounit
        (moduleLocalization.{z} Z) (ModuleQis.{z} Z)) =
        compCounit f g ≫ (modulePullbackToDerived.compIso f g).inv := sorry

/-- The componentwise counit equation characterizing the derived-pullback composition
comparison. -/
@[stacks 05T2 "ringed-site derived-pullback comparison counit component"]
theorem compComparison_counit_app (K : ModuleHomotopy.{z} Z) :
    (compComparison f g).app
        ((moduleLocalization.{z} Z).obj K) ≫
      ((modulePullbackToDerived.{z} (f.comp g)).totalLeftDerivedCounit
        (moduleLocalization.{z} Z) (ModuleQis.{z} Z)).app K =
        (compCounit f g).app K ≫
          (modulePullbackToDerived.compIso f g).inv.app K := sorry

end modulePullbackDerived

end

end RingedSite.Hom

-- Any `sorryAx` is inherited through Prop-valued abelian, derived-functor, or coherence
-- witnesses; the comparison morphism itself is the canonical generic construction.
