/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/-
Lemma 30.5.3 (Finite locally free base change): for a cartesian square over `Spec A` and
`Spec B`, extension of scalars along a finite locally free `A`-algebra identifies the
cohomology of a quasicoherent module with the cohomology of its pullback in every degree.
-/
@[stacks 0CKW] #check
  (AlgebraicGeometry.Scheme.Hom.cohomology_baseChange_of_finiteLocallyFree :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X Y : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A))
      (g : Y ⟶ Spec (CommRingCat.of B))
      (h : Y ⟶ X)
      (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
      [Module.FiniteLocallyFree A B]
      (F : X.Modules) [F.IsQuasicoherent] (i : ℕ),
      IsIsomorphic
        ((ModuleCat.extendScalars (algebraMap A B)).obj
          (AlgebraicGeometry.Scheme.Hom.cohomology f F i))
        (AlgebraicGeometry.Scheme.Hom.cohomology g
          ((Scheme.Modules.pullback h).obj F) i))
