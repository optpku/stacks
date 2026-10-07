module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Syzygy
public import ReasLib.RingTheory.Depth.CohenMacaulay

/-!
# Maximal Cohen--Macaulay syzygies

@stack 00NG

This leaf records the reusable syzygy consequence of the depth inequalities over a
Noetherian local Cohen--Macaulay ring.  The resolution and syzygy tower are owned by
`ChainComplex.Syzygy`; this file only supplies the depth-theoretic conclusion.  In
particular, the chosen-resolution theorem is separated from the existence theorem so
that downstream arguments can retain a resolution they already have.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex
namespace Syzygy

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/--
For a chosen finite free resolution of a finite module over a Noetherian local
Cohen--Macaulay ring, the syzygy at the codimension prescribed by the depth is
maximal Cohen--Macaulay.  The convention is `syzygy π 0 = M`, so the index is
the natural number `d - e` determined by `ringKrullDim R = d` and
`moduleDepth R M = e`.
-/
@[stacks 00NG "maximal Cohen--Macaulay syzygy for a chosen finite free resolution"]
theorem maximalCohenMacaulay_of_finiteFree
    {d e : ℕ} (hCM : Module.CohenMacaulay R R)
    (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e)
    {F : ChainComplex (ModuleCat.{v} R) ℕ}
    {π : F ⟶ moduleSingle R M} [IsFiniteFreeResolution π] :
    Module.MaximalCohenMacaulay R (syzygy π (d - e)) := sorry

/--
Lemma 10.104.9: there exists a finite free resolution whose `d - e`th syzygy is maximal
Cohen--Macaulay for every finite module of depth `e` over a local
Cohen--Macaulay ring of dimension `d`.
-/
@[stacks 00NG "existence of a maximal Cohen--Macaulay syzygy"]
theorem exists_maximalCohenMacaulay
    {d e : ℕ} (hCM : Module.CohenMacaulay R R)
    (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    ∃ (F : ChainComplex (ModuleCat.{v} R) ℕ)
      (π : F ⟶ moduleSingle R M),
      IsFiniteFreeResolution π ∧
        Module.MaximalCohenMacaulay R (syzygy π (d - e)) := sorry

end Syzygy
end ChainComplex
