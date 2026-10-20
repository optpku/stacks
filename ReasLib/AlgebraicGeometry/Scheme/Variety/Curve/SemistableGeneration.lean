module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizingSheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Neighbourhood generation of tensor powers of the relative dualizing sheaf

For a prestable family of curves of genus at least one, the fibre over a point
of the base has no rational tail if and only if some neighbourhood of that
point has `dualizingTensorPowerCounit f m` an epimorphism on the inverse
image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- For a proper at-worst-nodal family with universally invertible structure-sheaf
unit and a residue-field fibre of genus at least one, that fibre has no rational
tail if and only if every fixed tensor power of the relative dualizing sheaf of
exponent at least two is generated over an open neighbourhood of the base point
by the canonical pullback-pushforward counit. -/
@[stacks 0E6Y]
theorem no_rational_tail_iff_dualizingTensorPower_counit_epi
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 1 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ↔
      ∃ U : S.Opens, s ∈ U ∧
        Epi ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
          (dualizingTensorPowerCounit f m)) :=
  sorry

end AlgebraicGeometry
