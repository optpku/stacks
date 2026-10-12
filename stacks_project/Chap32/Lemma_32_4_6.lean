/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
public import ReasLib.Topology.Category.TopCat.Limits.Specialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/- Lemma 32.4.6 (1): in Situation 32.4.5, the underlying set of the limit scheme is the
inverse limit of the underlying sets of the stages. -/
@[stacks 01YY] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.bijective_sectionOfCone D c hc :
    Function.Bijective (Types.sectionOfCone (Scheme.forget.mapCone c)))

/- Lemma 32.4.6 (2): in Situation 32.4.5, the underlying topological space of the limit
scheme is the inverse limit of the underlying topological spaces of the stages. -/
@[stacks 01YY] #check
  (AlgebraicGeometry.isLimit_forgetToTop_mapCone_of_directedAffineTransition D c hc :
    IsLimit (Scheme.forgetToTop.mapCone c))

/- Lemma 32.4.6 (3): failure of specialization in the limit scheme is detected after
projection to one of the stages. -/
@[stacks 01YY] #check
  (TopCat.IsLimit.exists_not_specializes
      (Scheme.forgetToTop.mapCone c)
      (AlgebraicGeometry.isLimit_forgetToTop_mapCone_of_directedAffineTransition D c hc) :
    ∀ s s' : c.pt, ¬ s ⤳ s' →
      ∃ i : I, ¬ ((c.π.app i) s ⤳ (c.π.app i) s'))
