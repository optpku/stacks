/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.BoundedBelow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below cohomology of derived pushforwards

This leaf compares the canonical bounded-below pushforward with its unbounded restriction, then
forgets module structure.  The unbounded cohomology-presheaf and sheafification owners remain in
the parent `Cohomology` leaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology.BoundedBelow

variable {X Y : RingedSpace.{u}}

/-- The cohomology of bounded-below derived pushforward agrees canonically with the cohomology
of unbounded derived pushforward after applying `DerivedCategory.Plus.ι`. -/
@[stacks 05SA "bounded-below and unbounded pushforward cohomology comparison"]
noncomputable def cohomologyIso
    (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) (q : ℤ) :
    moduleDerivedPushforwardPlus.cohomology f K q ≅
      (moduleDerivedPushforward.cohomologyFunctor f q).obj
        (DerivedCategory.Plus.ι.obj K) :=
  (DerivedCategory.homologyFunctor Y.Modules q).mapIso
    ((CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso
      (AlgebraicGeometry.RingedSpace.Hom.pushforward f)).app K)

/-- The bounded/unbounded cohomology comparison after forgetting to additive sheaves. -/
@[stacks 05SA "underlying bounded-below pushforward cohomology comparison"]
noncomputable def underlyingCohomologyIso
    (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) (q : ℤ) :
    (moduleUnderlyingSheaf Y).obj
        (moduleDerivedPushforwardPlus.cohomology f K q) ≅
      (moduleUnderlyingSheaf Y).obj
        ((moduleDerivedPushforward.cohomologyFunctor f q).obj
          (DerivedCategory.Plus.ι.obj K)) :=
  (moduleUnderlyingSheaf Y).mapIso (cohomologyIso f K q)

/-- Companion to Lemma 20.7.3: for a bounded-below complex, the underlying additive
cohomology sheaf of derived pushforward is the sheafification of the inverse-image
hypercohomology presheaf. -/
@[stacks 01E4 "bounded-below derived pushforward from the cohomology presheaf"]
theorem underlying_isomorphic_sheafification
    (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) (q : ℤ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj
        (moduleDerivedPushforwardPlus.cohomology f K q))
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        (ModuleDerived.Pushforward.Cohomology.preimagePresheaf
          f (DerivedCategory.Plus.ι.obj K) q)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology.BoundedBelow

end
