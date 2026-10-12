/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_7_4_Class
public import stacks_project.Chap72.Lemma_72_7_5_MeromorphicSection

/-!
# Additivity of Weil divisors of meromorphic sections

On a locally Noetherian integral algebraic space, the Weil divisor of a tensor of
regular meromorphic sections is the sum of the Weil divisors, and the Weil divisor
class of a tensor of invertible modules is the sum of the classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- Lemma 72.7.5 (1): Let S be a scheme. Let X be a locally Noetherian integral algebraic
space over S. Let L, N be invertible 𝒪_X-modules. Let s, resp. t be a nonzero meromorphic
section of L, resp. N. Then st is a nonzero meromorphic section of L ⊗ N and
div_{L ⊗ N}(st) = div_L(s) + div_N(t) in Div(X). -/
@[stacks 0EPV]
theorem nonzeroMeromorphicSectionWeilDivisor_tensor
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t) :
    nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
      (isRegularMeromorphicSection_tensor s t hs ht) =
      nonzeroMeromorphicSectionWeilDivisor s hs +
        nonzeroMeromorphicSectionWeilDivisor t ht :=
  sorry

/-- The coefficient of the Weil divisor of a tensor of regular meromorphic sections along a
prime divisor is the sum of the coefficients of the factors. -/
theorem nonzeroMeromorphicSectionWeilDivisor_tensor_coeff
    {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t)
    (Z : PrimeDivisor X) :
    (nonzeroMeromorphicSectionWeilDivisor (meromorphicSectionTensor s t)
        (isRegularMeromorphicSection_tensor s t hs ht)).coeff Z =
      (nonzeroMeromorphicSectionWeilDivisor s hs).coeff Z +
        (nonzeroMeromorphicSectionWeilDivisor t ht).coeff Z :=
  sorry

/-- Lemma 72.7.5 (2): In particular, the Weil divisor class of L ⊗ N is the sum of the
Weil divisor classes of L and N. -/
@[stacks 0EPV]
theorem invertibleModuleWeilDivisorClass_tensor
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N] :
    invertibleModuleWeilDivisorClass (L ⊗ N) =
      invertibleModuleWeilDivisorClass L + invertibleModuleWeilDivisorClass N :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
