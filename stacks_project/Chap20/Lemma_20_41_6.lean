/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived.Hom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.41.6 is the source-faithful ringed-space specialization: `L` and `M` are arbitrary
derived objects and `Lc`, `Ic` are chosen representatives, with `Ic` K-injective. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

@[stacks 0A8R "restricted Hom-complex cohomology as local derived Hom"]
#check
  @OpenSubspace.Restriction.homologyZeroIsoOfIso X U

/- The source-facing `K↾[U]` target is owned by the same leaf; downstream proofs should not
reconstruct the endpoint transports from `derivedObjIsoRestricted`. -/
@[stacks 0A8R "intrinsic restricted derived-Hom comparison"]
#check @OpenSubspace.Restriction.homologyZeroIsoOfIso_restricted

#check @OpenSubspace.Restriction.homologyAddEquivOfIso
#check @OpenSubspace.Restriction.qObjRestrictionIsoOfIso

end AlgebraicGeometry.RingedSpace
