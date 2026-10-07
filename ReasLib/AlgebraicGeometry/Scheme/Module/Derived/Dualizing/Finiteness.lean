module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- For a Noetherian scheme with a dualizing complex, a coherent module satisfying `(S_k)` has
only finitely many points where its stalk depth is `k` and its stalk-support dimension is greater
than `k`. -/
@[stacks 0ECN]
theorem finite_setOf_depth_eq_and_lt_supportDim
    {X : Scheme.{u}} [IsNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω)
    (F : X.Modules) [F.IsCoherent] (k : ℕ)
    (hF : Scheme.Modules.satisfiesSerreConditionS F k) :
    Set.Finite {x : X |
      Scheme.Modules.hasDepthAt F x k ∧
        (k : WithBot ℕ∞) <
          Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)} := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
