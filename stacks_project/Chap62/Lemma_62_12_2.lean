module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TrivialRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback
public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_12_1

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

/-- The canonical map `E ⟶ D` in the zero-scheme square of `(ℒ, s)` along `f`. -/
noncomputable abbrev gysinPullbackMap :
    zeroScheme (gysinPullbackModule f ℒ) (gysinPullbackSection f ℒ s) ⟶
      zeroScheme ℒ s :=
  zeroSchemePullbackMap f.left ℒ s (zeroIdealSheaf_sectionsPullback f.left ℒ s)

/-- Unfolding `gysinPullbackModule` recovers module pullback of `ℒ` along `f.left`. -/
theorem gysinPullbackModule_def :
    gysinPullbackModule f ℒ =
      (Modules.pullback f.left).obj ℒ :=
  sorry

/-- Unfolding `gysinPullbackSection` recovers `sectionsPullback`. -/
theorem gysinPullbackSection_def :
    gysinPullbackSection f ℒ s = sectionsPullback f.left ℒ s :=
  sorry

/-- Unfolding `gysinPullbackMap` recovers `zeroSchemePullbackMap` of the
canonical zero-ideal identification. -/
theorem gysinPullbackMap_def :
    gysinPullbackMap f ℒ s =
      zeroSchemePullbackMap f.left ℒ s
        (zeroIdealSheaf_sectionsPullback f.left ℒ s) :=
  sorry

/-- The restriction of `ℒ` to its zero scheme `D`. -/
noncomputable abbrev gysinRestrictionModule : (zeroScheme ℒ s).Modules :=
  (Modules.pullback (zeroSchemeι ℒ s)).obj ℒ

/-- Unfolding `gysinRestrictionModule` recovers module pullback along
`zeroSchemeι ℒ s`. -/
theorem gysinRestrictionModule_def :
    gysinRestrictionModule ℒ s =
      (Modules.pullback (zeroSchemeι ℒ s)).obj ℒ :=
  sorry

/-- The structure morphism of `E` in the zero-scheme square is locally of
finite type over `S`. -/
instance gysinPullbackMap_toBase_locallyOfFiniteType :
    LocallyOfFiniteType (gysinPullbackMap f ℒ s ≫ zeroSchemeι ℒ s ≫ Y.hom) :=
  sorry

/-- Lemma 62.12.2: Let `(S, δ)` be as in the fibre-cycle action setup, and let
`f : X ⟶ Y` be a morphism of schemes locally of finite type over `S`. Let
`α` be a relative `r`-cycle on `X / Y`, and let `(ℒ, s)` be a Gysin pair on
`Y` whose restriction to `D = zeroScheme ℒ s` is trivial, so that the vertical
arrows are the cycle-level maps `trivialGysin`. Forming the cartesian square of
`zeroSchemePullbackSquare`, the identity
`j^* (α ∩ β) = (i^* α) ∩ (i^* β)` holds on cycles of `E`, where `α ∩ -` is
`cap`, `i^*α` is `FiberCycleFamily.baseChange` of that square, and `i^*`, `j^*`
are `trivialGysin` on `Y` and `X`. -/
@[stacks 0H6E]
theorem cap_trivialGysin
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : RelativeCycle.IsRelative α)
    (htriv : RingedSpace.IsTrivial (gysinRestrictionModule ℒ s))
    (e : ℤ) (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) (e + 1)) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι (gysinPullbackModule f ℒ) (gysinPullbackSection f ℒ s) ≫
          f.left ≫ Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (trivialGysin (f.left ≫ Y.hom) δ (gysinPullbackModule f ℒ)
          (gysinPullbackSection f ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) ((r : ℤ) + e)
          (CycleGroup.reindex ((f.left ≫ Y.hom).relativeDimensionFunction δ)
            (add_assoc (r : ℤ) e 1).symm (cap Y.hom f.left δ α β))) =
      CycleGroup.toAlgebraicCycle
        ((gysinPullbackMap f ℒ s ≫ zeroSchemeι ℒ s ≫
          Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap (zeroSchemeι ℒ s ≫ Y.hom) (gysinPullbackMap f ℒ s) δ
          (FiberCycleFamily.baseChange (zeroSchemePullbackSquare f.left ℒ s) α)
          (trivialGysin Y.hom δ ℒ s htriv e β)) :=
  sorry

/-- Evaluating `cap_trivialGysin` compares coefficients of both sides at a point
of the zero scheme of the pulled-back section. -/
theorem cap_trivialGysin_apply
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : RelativeCycle.IsRelative α)
    (htriv : RingedSpace.IsTrivial (gysinRestrictionModule ℒ s))
    (e : ℤ) (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) (e + 1))
    (z : zeroScheme (gysinPullbackModule f ℒ) (gysinPullbackSection f ℒ s)) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι (gysinPullbackModule f ℒ) (gysinPullbackSection f ℒ s) ≫
          f.left ≫ Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (trivialGysin (f.left ≫ Y.hom) δ (gysinPullbackModule f ℒ)
          (gysinPullbackSection f ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) ((r : ℤ) + e)
          (CycleGroup.reindex ((f.left ≫ Y.hom).relativeDimensionFunction δ)
            (add_assoc (r : ℤ) e 1).symm (cap Y.hom f.left δ α β))) z =
      CycleGroup.toAlgebraicCycle
        ((gysinPullbackMap f ℒ s ≫ zeroSchemeι ℒ s ≫
          Y.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (cap (zeroSchemeι ℒ s ≫ Y.hom) (gysinPullbackMap f ℒ s) δ
          (FiberCycleFamily.baseChange (zeroSchemePullbackSquare f.left ℒ s) α)
          (trivialGysin Y.hom δ ℒ s htriv e β)) z :=
  sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
