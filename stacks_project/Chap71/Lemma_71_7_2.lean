module

public import stacks_project.Chap71.Lemma_71_7_2_Comparison

/-!
# Lemma 71.7.2

The conormal sheaf of an effective Cartier divisor on an algebraic space is the
restriction of its negative/ideal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.Conormal

/-- Lemma 71.7.2. Let `S` be a scheme, let `X` be an algebraic space over `S`, and
let `i : D ⟶ X` be an effective Cartier divisor. Then the conormal sheaf
`Hom.conormalSheaf i` is canonically the restriction `(Modules.pullback i).obj`
of the ideal sheaf `Hom.idealSheaf i`, equivalently of `Hom.negSheaf i` which
is `𝒪_X(D)^{⊗ -1}`. -/
@[stacks 0B4F]
theorem pullbackIdealComparison_isIso {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) [IsEffectiveCartierDivisor i] :
    IsIso
      (pullbackIdealComparison i :
        (Modules.pullback i).obj (negSheaf i) ⟶ conormalSheaf i) :=
  sorry

end Hom.Conormal

end AlgebraicGeometry.AlgebraicSpace
