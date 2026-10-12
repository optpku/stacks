/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_21_4_Homology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace Hom
namespace NaiveCotangent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : ℤ)

/- Lemma 76.21.4 (1): every homology sheaf of the naive cotangent complex of a
morphism of algebraic spaces is quasi-coherent. -/
@[stacks 0D0Y] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homology_isQuasicoherent f i :
    ((NL[f]).homology i).IsQuasicoherent)

variable (hi_zero : i ≠ 0) (hi_negOne : i ≠ -1)

/- Lemma 76.21.4 (2): the homology of the naive cotangent complex of a morphism of
algebraic spaces is zero outside degrees `-1` and `0`. -/
@[stacks 0D0Y] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homology_isZero_of_ne_zero_or_negOne
    f i hi_zero hi_negOne : IsZero ((NL[f]).homology i))

/- Lemma 76.21.4 (3): degree-zero homology of the naive cotangent complex is
canonically isomorphic to the sheaf of relative differentials. -/
@[stacks 0D0Y] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homologyZeroIso f :
    (NL[f]).homology 0 ≅ Ω[f])

end NaiveCotangent
end Hom
end AlgebraicSpace
end AlgebraicGeometry
