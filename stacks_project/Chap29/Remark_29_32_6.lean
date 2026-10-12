/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineOpenBasis
import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
import StacksCheckRecall

open CategoryTheory Opposite
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Remark 29.32.6: the affine opens `U ⊆ X` that map into an affine open of `S` form a basis
for the topology on `X`. On each compatible affine pair, sections of `Ω[f.toShHom]` are
canonically linearly equivalent to the Kähler differentials of the induced map on sections. -/
@[stacks 01UU] #check
  (AlgebraicGeometry.Scheme.Hom.isBasis_affineOpens_mappingIntoAffineOpen f :
    TopologicalSpace.Opens.IsBasis
      {U : X.Opens | IsAffineOpen U ∧ ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V})

variable (U : X.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)

#check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.existsUnique_affineSectionsLinearEquiv
      f U V hU hV hUV :
    ∃! eΩ :
      Γ(Ω[f.toShHom], U) ≃ₗ[Γ(X, U)]
        CommRingCat.KaehlerDifferential (f.appLE V U hUV),
      ∀ a : Γ(X, U),
        eΩ (((d[f.toShHom]).app (op U)).d a) =
          CommRingCat.KaehlerDifferential.d a)

end AlgebraicGeometry
