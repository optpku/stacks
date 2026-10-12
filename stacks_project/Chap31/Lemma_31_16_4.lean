/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OpenComplement.Dimension

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 31.16.4: for a locally Noetherian scheme and an open subscheme whose inclusion is
affine, the local ring at a generic point of the complement has Krull dimension at most one. -/
@[stacks 0BCU] #check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_le_one_of_isAffineHom_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }},
      ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } →
        ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1)

/- Under the same hypotheses, closure membership forces the local ring at the complement
generic point to have Krull dimension one. -/
#check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_eq_one_of_mem_closure :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }},
      ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } → ξ.1 ∈ closure (U : Set X) →
        ringKrullDim (X.presheaf.stalk ξ.1) = 1)

/- Under the same hypotheses, density of the open subscheme forces the local ring at every
complement generic point to have Krull dimension one. -/
#check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_eq_one_of_isAffineHom_of_mem_genericPoints_of_dense :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }},
      ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } → Dense (U : Set X) →
        ringKrullDim (X.presheaf.stalk ξ.1) = 1)
