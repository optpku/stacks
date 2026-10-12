/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation

/-!
# Valuation base change and irreducible components of fibers

This file records a valuation-spectrum base change that lifts generic points
of irreducible components in fibers of reduced point closures.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If `y : X` lies over `t : S` and `x` is the generic point of an irreducible
component of the `s`-fiber of the reduced closure of `y`, then a valuation-spectrum base
change of `f : X ⟶ S` has a generic-fiber component above `y` whose reduced closure has
a closed-fiber component above `x`. -/
@[stacks 0GSH]
theorem exists_valuationBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (y : X) (t s : S)
    (hy : f y = t)
    (x : (PointClosure.ι y ≫ f).fiber s)
    (hx : closure ({x} : Set ((PointClosure.ι y ≫ f).fiber s)) ∈
      irreducibleComponents ((PointClosure.ι y ≫ f).fiber s)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (g : Spec (CommRingCat.of A) ⟶ S),
      let t' := genericPoint (Spec (CommRingCat.of A))
      let s' := IsLocalRing.closedPoint A
      g t' = t ∧ g s' = s ∧
        let pY := pullback.fst g (PointClosure.ι y ≫ f)
        ∃ y' : pY.fiber t',
          closure ({y'} : Set (pY.fiber t')) ∈ irreducibleComponents (pY.fiber t') ∧
          let yX' := (pY.fiberι t' ≫ PointClosure.baseChangeMap f g y) y'
          pullback.snd g f yX' = y ∧
            let pY' := PointClosure.ι yX' ≫ pullback.fst g f
            ∃ x' : pY'.fiber s',
              closure ({x'} : Set (pY'.fiber s')) ∈ irreducibleComponents (pY'.fiber s') ∧
                (pY'.fiberι s' ≫ PointClosure.ι yX' ≫ pullback.snd g f) x' =
                  ((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x := sorry

end AlgebraicGeometry.Scheme.Hom
