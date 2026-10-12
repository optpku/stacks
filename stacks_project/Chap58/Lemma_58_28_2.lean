/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Purity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 58.28.2: a finite type morphism to the spectrum of an excellent
regular local ring, étale away from the closure of a normal two-dimensional
stalk, is étale at that point. -/
@[stacks 0EA3] #check (AlgebraicGeometry.Scheme.Hom.etaleAt_of_purity :
  ∀ (A : Type u) [CommRing A] [IsExcellentRing A] [IsRegularLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [Scheme.Hom.FiniteType f]
    (x : X) (h_normal : X.isNormalAt x)
    (h_dimension : ringKrullDim (X.presheaf.stalk x) = 2)
    (h_etale_off_closure :
      ∀ y : X, y ∉ closure ({x} : Set X) → f.EtaleAt y),
    f.EtaleAt x)
