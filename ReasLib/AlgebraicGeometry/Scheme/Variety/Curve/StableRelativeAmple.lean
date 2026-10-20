module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail

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
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If the relative dualizing sheaf is relatively ample over some open
neighbourhood of a base point, then the residue-field fibre has neither a
rational tail nor a rational bridge. -/
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

/-- If the residue-field fibre has neither a rational tail nor a rational
bridge, then the relative dualizing sheaf is relatively ample over some open
neighbourhood of the base point. -/
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

/-- For a prestable family of curves of genus at least two, the residue-field
fibre has neither a rational tail nor a rational bridge if and only if the
relative dualizing sheaf is relatively ample over some open neighbourhood of
the given base point. -/
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
