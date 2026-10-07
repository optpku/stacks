module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OpenComplement.Dimension

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 31.16.5: let `X` be a separated locally Noetherian scheme and let `U ⊆ X` be an
affine open. For every generic point `ξ` of an irreducible component of `X \ U`, the local ring
at `ξ` has Krull dimension at most one. -/
@[stacks 0BCV] #check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_le_one_of_isAffineOpen_of_isSeparated :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
      {U : X.Opens}, IsAffineOpen U → ∀ {ξ : { x : X // x ∉ (U : Set X) }},
        ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } →
          ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1)

/- Under the same hypotheses, if the complement generic point lies in the closure of the affine
open, then its local ring has Krull dimension one. -/
#check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_eq_one_of_isAffineOpen_of_mem_closure_of_isSeparated :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
      {U : X.Opens}, IsAffineOpen U → ∀ {ξ : { x : X // x ∉ (U : Set X) }},
        ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } →
          ξ.1 ∈ closure (U : Set X) → ringKrullDim (X.presheaf.stalk ξ.1) = 1)

/- Under the same hypotheses, if the affine open is dense, then every complement generic point
has local ring of Krull dimension one. -/
#check
  (AlgebraicGeometry.Scheme.OpenComplement.ringKrullDim_stalk_eq_one_of_isAffineOpen_of_dense_of_isSeparated :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
      {U : X.Opens}, IsAffineOpen U → ∀ {ξ : { x : X // x ∉ (U : Set X) }},
        ξ ∈ genericPoints { x : X // x ∉ (U : Set X) } → Dense (U : Set X) →
          ringKrullDim (X.presheaf.stalk ξ.1) = 1)
