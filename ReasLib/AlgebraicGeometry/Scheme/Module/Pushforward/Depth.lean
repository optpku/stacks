module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

/-!
# Depth and regularity of pushforward stalks

This file records depth bounds and transfer of regular elements to stalks of pushforwards along
quasi-compact and quasi-separated morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward

variable {X S : Scheme.{u}}
variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The pushforward stalk at a point outside the range of a quasi-compact and quasi-separated
morphism has depth at least two when the target stalk is Noetherian and the module stalk is
finite. -/
theorem moduleDepth_stalk_ge_two_of_not_mem_range
    (s : S) [IsNoetherianRing (S.presheaf.stalk s)]
    [Module.Finite (S.presheaf.stalk s)
      (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)]
    (hs : s ∉ Set.range f.base) :
    (2 : ℕ∞) ≤ moduleDepth (S.presheaf.stalk s)
      (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) := sorry

/-- If a quasicoherent module is flat over the base, a regular element in the maximal ideal of a
target stalk acts regularly on the corresponding pushforward stalk. -/
theorem isSMulRegular_stalk_of_flatOver
    (hflat : flatOver ℱ f)
    (s : S) (a : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (ha : IsSMulRegular (S.presheaf.stalk s) a) :
    IsSMulRegular
      (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) a := sorry

/-- If a pair in the maximal ideal is a regular sequence and a quasicoherent module is flat over
the base, the first element acts regularly on the corresponding pushforward stalk. -/
theorem isSMulRegular_stalk_first_of_flatOver_of_isRegular_pair
    (hflat : flatOver ℱ f)
    (s : S) (a b : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hb_mem : b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hab : RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b]) :
    IsSMulRegular
      (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) a := sorry

/-- If a pair in the maximal ideal is a regular sequence and a quasicoherent module is flat over
the base, the second element acts regularly on the quotient of the corresponding pushforward
stalk by the first element. -/
theorem isSMulRegular_quotSMulTop_stalk_second_of_flatOver_of_isRegular_pair
    (hflat : flatOver ℱ f)
    (s : S) (a b : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hb_mem : b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hab : RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b]) :
    IsSMulRegular
      (QuotSMulTop a
        (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)) b := sorry

/-- If a quasicoherent module is flat over the base and its pushforward stalk is finite, the
stalk depth is at least the minimum of two and the depth of the target local ring. -/
theorem moduleDepth_stalk_ge_min_two_of_flatOver
    (hflat : flatOver ℱ f)
    (s : S)
    [Module.Finite (S.presheaf.stalk s)
      (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)] :
    min (2 : ℕ∞) (moduleDepth (S.presheaf.stalk s) (S.presheaf.stalk s)) ≤
      moduleDepth (S.presheaf.stalk s)
        (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) := sorry

end AlgebraicGeometry.Scheme.Modules.Pushforward
