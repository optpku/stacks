module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import stacks_project.Chap109.Lemma_109_21_1_RelativeDualizing

/-!
# Neighbourhood ampleness of the relative dualizing sheaf

For a prestable family of curves of genus at least two, the fibre over a
point of the base has neither a rational tail nor a rational bridge if and
only if the relative dualizing sheaf is relatively ample over some open
neighbourhood of that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If the relative dualizing sheaf is relatively ample over some open
neighbourhood of `s`, then the fibre over `s` has neither a rational tail nor
a rational bridge. -/
theorem no_rational_tail_no_rational_bridge_of_relativeDualizing_ample
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 2 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    (h : ∃ U : S.Opens, s ∈ U ∧
      RelativelyAmple (f ∣_ U)
        (restrictToBasePreimage f (relativeDualizingSheaf f) U)) :
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ∧
      ¬ Nonempty (RationalBridge (Over.mk (f.fiberToSpecResidueField s))) :=
  sorry

/-- If the fibre over `s` has neither a rational tail nor a rational bridge,
then the relative dualizing sheaf is relatively ample over some open
neighbourhood of `s`. -/
theorem relativeDualizing_ample_of_no_rational_tail_no_rational_bridge
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 2 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    (h : ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ∧
      ¬ Nonempty (RationalBridge (Over.mk (f.fiberToSpecResidueField s)))) :
    ∃ U : S.Opens, s ∈ U ∧
      RelativelyAmple (f ∣_ U)
        (restrictToBasePreimage f (relativeDualizingSheaf f) U) :=
  sorry

/-- Lemma 109.22.1: for a prestable family of curves `f : X ⟶ S` of genus at
least two and a point `s` of `S`, the fibre
`Over.mk (f.fiberToSpecResidueField s)` has neither a rational tail nor a
rational bridge if and only if `relativeDualizingSheaf f` is relatively ample
over `U` (ample on `f ⁻¹ᵁ U / U`) for some open neighbourhood `U` of `s`. -/
@[stacks 0E74]
theorem no_rational_tail_no_rational_bridge_iff_relativeDualizing_ample
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 2 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1) :
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ∧
        ¬ Nonempty (RationalBridge (Over.mk (f.fiberToSpecResidueField s))) ↔
      ∃ U : S.Opens, s ∈ U ∧
        RelativelyAmple (f ∣_ U)
          (restrictToBasePreimage f (relativeDualizingSheaf f) U) :=
  sorry

end AlgebraicGeometry
