module

public import stacks_project.Chap82.Definition_82_13_1_PrincipalDivisor
public import stacks_project.Chap82.Lemma_82_8_2_Pushforward
public import stacks_project.Chap82.Lemma_82_14_1_Norm

/-!
# Proper pushforward of principal divisors on algebraic spaces

In Situation 82.2.1, a dominant proper morphism of good integral algebraic
spaces of equal `δ`-dimension sends a principal divisor to the principal
divisor of the induced function-field norm.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable [IsIntegral X]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- Lemma 82.14.1: In Situation 82.2.1 let `X`, `Y / B` be good. Assume `X`, `Y`
are integral and `n = dim_δ(X) = dim_δ(Y)`. Let `p : X ⟶ Y` be a dominant proper
morphism. Let `φ ∈ (RationalFunction X)ˣ`. Set `g = Nm_{R(X)/R(Y)}(φ)`, the
image of `φ` under `inducedRationalFunctionNorm p`. Then `p_* div(φ) = div(g)`. -/
@[stacks 0EQ4]
theorem properPushforward_principalDivisor {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (p : X ⟶ Y) [Proper p] [Dominant p] (hp : p ≫ pY = f)
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (φ : (RationalFunction X)ˣ) :
    properPushforwardHom f pY δ p hp (n - 1) (principalDivisor f δ n hX φ) =
      principalDivisor pY δ n hY (inducedRationalFunctionNorm p φ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
