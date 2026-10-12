/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Countable
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

/- Lemma 57.17.3 (1): if `X` is a scheme of finite type over a countable
Noetherian ring, then the category of perfect complexes on `X` is countable. -/
@[stacks 0G0W] #check
  (AlgebraicGeometry.Scheme.countableCategory_perfect :
    ∀ {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
      (X : Scheme.FiniteTypeOver (Spec (CommRingCat.of R))),
      CountableCategory
        (Skeleton
          (@ModuleDerived.Perfect (Over.left X.obj).toRingedSpace)))

/- Lemma 57.17.3 (2): if `X` is a scheme of finite type over a countable
Noetherian ring, then the bounded derived category with coherent cohomology on
`X` is countable. -/
@[stacks 0G0W] #check
  (AlgebraicGeometry.Scheme.countableCategory_boundedCoherent :
    ∀ {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
      (X : Scheme.FiniteTypeOver (Spec (CommRingCat.of R))),
      CountableCategory
        (Skeleton
          (DerivedCategory.Bounded.CohomologyIn
            (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))))
