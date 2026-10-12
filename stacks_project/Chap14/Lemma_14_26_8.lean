/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.DeltaOne.Contraction
import StacksCheckRecall

/-!
@stack 019O

# Source-facing bridge for Lemma 14.26.8

The endpoint maps and contractions of the simplicial copower cylinder are owned by the neutral
`SimplicialObject.copower.deltaOne` API. Its construction factors through the reusable
`SSet.deltaOne.max.homotopy` and `SSet.deltaOne.min.homotopy` data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
variable (U : SimplicialObject C)

/- Lemma 14.26.8 (1): the zero endpoint is a section of the simplicial-cylinder projection. -/
@[stacks 019O]
#check (copower.deltaOne.endpointZero.comp_projection (X := U) :
  copower.deltaOne.endpointZero U ≫ copower.projection U (Δ[1] : SSet.{0}) = 𝟙 U)

/- Lemma 14.26.8 (2): the one endpoint is also a section of the simplicial-cylinder projection. -/
@[stacks 019O]
#check (copower.deltaOne.endpointOne.comp_projection (X := U) :
  copower.deltaOne.endpointOne U ≫ copower.projection U (Δ[1] : SSet.{0}) = 𝟙 U)

/- Lemma 14.26.8 (3): the cylinder identity is homotopic to projection followed by the zero
endpoint. -/
@[stacks 019O]
#check (copower.deltaOne.endpointZero.id_homotopic_projection (X := U) :
  Homotopic (𝟙 (copower (Δ[1] : SSet.{0}) U))
    (copower.projection U (Δ[1] : SSet.{0}) ≫ copower.deltaOne.endpointZero U))

/- Lemma 14.26.8 (4): the cylinder identity is homotopic to projection followed by the one
endpoint. -/
@[stacks 019O]
#check (copower.deltaOne.endpointOne.id_homotopic_projection (X := U) :
  Homotopic (𝟙 (copower (Δ[1] : SSet.{0}) U))
    (copower.projection U (Δ[1] : SSet.{0}) ≫ copower.deltaOne.endpointOne U))

/- Structured companion: the projection has a canonical split-epi structure, selected at the
zero endpoint. -/
#check (copower.deltaOne.projection.splitEpi U :
  SplitEpi (copower.projection U (Δ[1] : SSet.{0})))

/- Structured companion: either endpoint exhibits the cylinder projection as a simplicial
homotopy equivalence. -/
variable (i : Fin 2)

#check (copower.deltaOne.projection.homotopyEquiv U i :
  HomotopyEquiv (copower (Δ[1] : SSet.{0}) U) U)

end CategoryTheory.SimplicialObject
