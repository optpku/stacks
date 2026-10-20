/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Gysin

/-!
# Compatibility of the fibre-cycle action with trivial-restriction Gysin

This file records that forming `α ∩ β` commutes with the cycle-level Gysin maps
of a trivial-restriction pair along the cartesian zero-scheme square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme (Modules)
open AlgebraicGeometry.Scheme.Modules hiding pullback

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (f : X ⟶ Y) [LocallyOfFiniteType f.left] [IsLocallyNoetherian Y.left]
variable (ℒ : Y.left.Modules) [Invertible ℒ] (s : ℒ.sections)

/-- The pullback of `ℒ` along the displayed morphism `f.left`. -/
noncomputable abbrev gysinPullbackModule : X.left.Modules :=
  (Modules.pullback f.left).obj ℒ

/-- The pullback of a section of `ℒ` along the displayed morphism `f.left`. -/
noncomputable abbrev gysinPullbackSection : (gysinPullbackModule f ℒ).sections :=
  sectionsPullback f.left ℒ s

/-- The restriction of `ℒ` to its zero scheme `D`. -/
noncomputable abbrev gysinRestrictionModule : (zeroScheme ℒ s).Modules :=
  (Modules.pullback (zeroSchemeι ℒ s)).obj ℒ

/- Lemma 62.12.2: Let `(S, δ)` be as in the fibre-cycle action setup, and let
`f : X ⟶ Y` be a morphism of schemes locally of finite type over `S`. Let
`α` be a relative `r`-cycle on `X / Y`, and let `(ℒ, s)` be a Gysin pair on
`Y` whose restriction to `D = zeroScheme ℒ s` is trivial, so that the vertical
arrows are the cycle-level maps `trivialGysin`. Forming the cartesian square of
`zeroSchemePullbackSquare`, the identity
`j^* (α ∩ β) = (i^* α) ∩ (i^* β)` holds on cycles of `E`, where `α ∩ -` is
`cap`, `i^*α` is `FiberCycleFamily.baseChange` of that square, and `i^*`, `j^*`
are `trivialGysin` on `Y` and `X`. -/
@[stacks 0H6E] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_trivialGysin :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] [IsLocallyNoetherian Y.left]
    (ℒ : Y.left.Modules) [Invertible ℒ] (s : ℒ.sections)
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : RelativeCycle.IsRelative α)
    (htriv : RingedSpace.IsTrivial ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ))
    (e : ℤ) (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) (e + 1)),
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ((Modules.pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫
          f.left ≫ Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (trivialGysin (f.left ≫ Y.hom) δ ((Modules.pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) ((r : ℤ) + e)
          (CycleGroup.reindex ((f.left ≫ Y.hom).relativeDimensionFunction δ)
            (add_assoc (r : ℤ) e 1).symm (cap Y.hom f.left δ α β))) =
      CycleGroup.toAlgebraicCycle
        ((zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s) ≫ zeroSchemeι ℒ s ≫
          Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap (zeroSchemeι ℒ s ≫ Y.hom) (zeroSchemePullbackMap f.left ℒ s
          (zeroIdealSheaf_sectionsPullback f.left ℒ s)) δ
          (FiberCycleFamily.baseChange (zeroSchemePullbackSquare f.left ℒ s) α)
          (trivialGysin Y.hom δ ℒ s htriv e β)))

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
