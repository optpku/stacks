/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology.BoundedBelow
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Presheaf
open AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology

/- Lemma 20.7.3: the underlying additive sheaf of a higher direct image is the sheafification of
the pushed-forward cohomology presheaf. -/
@[stacks 01E4 "higher direct image from the cohomology presheaf"]
#check @underlying_isomorphic_sheafification
#check @functor_isomorphic_sheafification

-- The bounded-below companion uses the canonical bounded/unbounded comparison before
-- sheafifying the inverse-image hypercohomology presheaf.
#check @BoundedBelow.cohomologyIso
#check @BoundedBelow.underlyingCohomologyIso
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.Cohomology.BoundedBelow.underlying_isomorphic_sheafification

-- Generic owners retained at the two reusable layers.
#check @TopCat.Sheaf.HigherDirectImage.Presheaf.objIso
#check @CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso
