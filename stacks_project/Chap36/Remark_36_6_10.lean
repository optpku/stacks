module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Remark 36.6.10: the canonical `𝒪_X|_Z`-linear map from the quotient presentation of
`i^*ℱ` to `H^c_Z(ℱ)`, functorial in `ℱ`, is induced after pushforward by the top Čech
fraction class `s ↦ [s/(∏ i, f i)]` and the derived Čech-to-supported-cohomology comparison. -/
@[stacks 0G7Q] #check (ModuleCech.LocalCohomology.quotientClassMap :
  ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)),
    ModuleCech.LocalCohomology.zeroLocusPullback f ⟶
      ModuleCech.LocalCohomology.cohomologyFunctor f)

#check ModuleCech.LocalCohomology.quotientClassMap_pushforward
#check ModuleCech.LocalCohomology.cechClass_π
