module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Valuation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

/- Lemma 37.18.2: if `y : X` lies over `t : S` and `x` is the generic point of an
irreducible component of the `s`-fiber of the reduced closure of `y`, then a valuation-spectrum
base change of `f : X ⟶ S` has a generic-fiber component above `y` whose reduced closure has
a closed-fiber component above `x`. -/
@[stacks 0GSH]
#check (AlgebraicGeometry.Scheme.Hom.exists_valuationBaseChange :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (y : X) (t s : S)
    (hy : f y = t)
    (x : (PointClosure.ι y ≫ f).fiber s)
    (hx : closure ({x} : Set ((PointClosure.ι y ≫ f).fiber s)) ∈
      irreducibleComponents ((PointClosure.ι y ≫ f).fiber s)),
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
                  ((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x)
