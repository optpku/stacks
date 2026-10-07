module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Homology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NaiveCotangent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℤ)

/- Lemma 37.13.3 (1): every homology sheaf of the naive cotangent complex of a
scheme morphism is quasi-coherent. -/
@[stacks 0D0J] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.homology_isQuasicoherent f i :
    ((NL[f.toShHom]).homology i).IsQuasicoherent)

variable (hi_zero : i ≠ 0) (hi_negOne : i ≠ -1)

/- Lemma 37.13.3 (2): the homology of the naive cotangent complex of a scheme
morphism is zero outside degrees `-1` and `0`. -/
@[stacks 0D0J] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.homology_isZero_of_ne_zero_or_negOne
    f i hi_zero hi_negOne : IsZero ((NL[f.toShHom]).homology i))

/- Lemma 37.13.3 (3): degree-zero homology of the naive cotangent complex is
canonically isomorphic to the sheaf of relative differentials. -/
@[stacks 0D0J] #check
  (AlgebraicGeometry.RingedSpace.NaiveCotangent.homologyZeroIso f.toShHom :
    (NL[f.toShHom]).homology 0 ≅ Ω[f.toShHom])

end NaiveCotangent
end Hom
end Scheme
end AlgebraicGeometry
