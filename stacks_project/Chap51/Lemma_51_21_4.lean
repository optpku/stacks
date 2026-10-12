/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.Annihilation
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Scheme.Modules
open AffineBaseModuleDerivedAdjunction
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

/- Lemma 51.21.4: if `t` bounds the number of generators of the center ideal `I`,
then one power of the exceptional ideal annihilates every degree-`j` cohomology sheaf of
`Lp^* M̃`, uniformly for all `A`-modules `M` and all `j ≤ -t`. -/
@[stacks 0GA0]
#check (AlgebraicGeometry.IsBlowup.derivedPullbackCohomology_isAnnihilated :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    [HasLeftDerived A p]
    (t : ℕ)
    (h_generators : ∃ a : Fin t → I,
      I = Ideal.span (Set.range fun i ↦ (a i : A))),
    ∃ c : ℕ, ∀ (M : ModuleCat A) (j : ℤ), j ≤ -(t : ℤ) →
      @IsAnnihilated
        (Opens X.toRingedSpace) _ (Opens.grothendieckTopology X.toRingedSpace) _
        X.toRingedSpace.sheaf
        ((((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject)
        ((DerivedCategory.homologyFunctor X.Modules j).obj
          ((affineBaseModuleDerivedAssociatedFunctor A p).obj
            ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M))))
