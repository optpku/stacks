/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.StableRelativeAmple
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 109.22.1: for a prestable family of curves of genus at least two, the
residue-field fibre has neither a rational tail nor a rational bridge if and only
if the relative dualizing sheaf is relatively ample over some open neighbourhood
of the given base point. -/
@[stacks 0E74] #check (AlgebraicGeometry.no_rational_tail_no_rational_bridge_iff_relativeDualizing_ample :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 2 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1),
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ∧
        ¬ Nonempty (RationalBridge (Over.mk (f.fiberToSpecResidueField s))) ↔
      ∃ U : S.Opens, s ∈ U ∧
        RelativelyAmple (f ∣_ U)
          (restrictToBasePreimage f (relativeDualizingSheaf f) U))
