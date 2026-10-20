module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle
import StacksCheckRecall

/-!
# Coefficient of an integral closed subspace in a module cycle

In the good setup of Situation 82.2.1, the coefficient of an integral closed
subspace of relative dimension `k` in the associated `k`-cycle of a coherent
module is the length of that module at the generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.6.2: In Situation 82.2.1, let `X / B` be good. Let `F` be a coherent
`𝒪_X`-module with `dim_δ(Supp(F)) ≤ k`. Let `Z` be an integral closed subspace of
`X` with `dim_δ(Z) = k`. Let `ξ ∈ |Z|` be the generic point. Then the coefficient
of `Z` in `[F]_k` is the length of `F` at `ξ`. -/
@[stacks 0EEC]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle_eq_lengthAt :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (F : X.Modules) [F.IsCoherent]
    (k : ℤ) (hF : (moduleSupportDeltaDimension f) δ F ≤ (k : EInt))
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : (closedSubspaceDeltaDimension f) δ Z = (k : EInt))
    (ξ : Points X) (hξ : IsGenericPoint ξ Z.pointsSet),
    moduleCycle f δ F k hF ξ = (Modules.lengthAt F ξ).toNat)

end AlgebraicGeometry.AlgebraicSpace.Hom
