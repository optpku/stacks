/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.Slicing

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.23.2: a regular sequence in the fibre stalk of a morphism that is
locally of finite presentation and flat at `x` lifts on an affine neighbourhood
to equations for a regular immersion that is flat and locally of finite
presentation over the base, and remains regular after every base change. -/
@[stacks 06LI]
#check (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_regularImmersion_of_fiber_regularSequence :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (r : ℕ) (h : Fin r → X.presheaf.stalk x)
    (hflat : f.flatAt x)
    (hreg : RingTheory.Sequence.IsRegular
      (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x)
      (List.ofFn fun i ↦
        (AlgebraicGeometry.Scheme.Hom.sourceStalkToFiberStalk f x).hom (h i))),
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ hU : Fin r → Γ(X, (U : X.Opens)),
          (∀ i, X.presheaf.germ (U : X.Opens) x hxU (hU i) = h i) ∧
            let Z : (U : X.Opens).toScheme.IdealSheafData :=
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span (Set.range fun i ↦ (U : X.Opens).topIso.inv (hU i)))
            (⟨x, hxU⟩ ∈ Z.support ∧
              IsRegularImmersion Z.subschemeι ∧
                Flat (Z.subschemeι ≫ ((U : X.Opens).ι ≫ f)) ∧
                  LocallyOfFinitePresentation (Z.subschemeι ≫ ((U : X.Opens).ι ≫ f)) ∧
                    ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
                      IsRegularImmersion
                        (pullback.snd Z.subschemeι
                          (pullback.fst ((U : X.Opens).ι ≫ f) g))))
