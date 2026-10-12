/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Affine
public import ReasLib.AlgebraicGeometry.Noetherian.Topology
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal

/-!
# Dimension at generic points of open complements

Dimension bounds for local rings at generic points of the complement of an open subscheme
whose inclusion is affine.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.OpenComplement

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A generic point of the complement of an open subscheme with affine inclusion has local
ring of Krull dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_isAffineHom_of_mem_genericPoints
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) }) :
    ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1 := sorry

/-- A generic point of the complement lying in the closure of an open subscheme with affine
inclusion has local ring of Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_mem_closure
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) })
    (hξ_closure : ξ.1 ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

/-- If an open subscheme with affine inclusion is dense, then a generic point of its complement
has local ring of Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isAffineHom_of_mem_genericPoints_of_dense
    {U : X.Opens} [IsAffineHom U.ι] {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) })
    (hU_dense : Dense (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

/-- In a separated scheme, a generic point of the complement of an affine open has local ring
of Krull dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_isAffineOpen_of_isSeparated
    [X.IsSeparated] {U : X.Opens} (hU : IsAffineOpen U)
    {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) }) :
    ringKrullDim (X.presheaf.stalk ξ.1) ≤ 1 := sorry

/-- In a separated scheme, a generic point of the complement of an affine open that lies in
the closure of the open has local ring of Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isAffineOpen_of_mem_closure_of_isSeparated
    [X.IsSeparated] {U : X.Opens} (hU : IsAffineOpen U)
    {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) })
    (hξ_closure : ξ.1 ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

/-- In a separated scheme, a generic point of the complement of a dense affine open has local
ring of Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isAffineOpen_of_dense_of_isSeparated
    [X.IsSeparated] {U : X.Opens} (hU : IsAffineOpen U)
    {ξ : { x : X // x ∉ (U : Set X) }}
    (hξ : ξ ∈ genericPoints { x : X // x ∉ (U : Set X) })
    (hU_dense : Dense (U : Set X)) :
    ringKrullDim (X.presheaf.stalk ξ.1) = 1 := sorry

end AlgebraicGeometry.Scheme.OpenComplement
