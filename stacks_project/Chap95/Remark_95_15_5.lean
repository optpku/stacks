/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Remark_95_15_5_Comparison
public import stacks_project.Chap95.Remark_95_15_5_Quotient

/-!
# Remark 95.15.5

The stack in groupoids `[[X/G]]` attached to an algebraic space with an
abstract group action, the representability of `underline(G)` by `G_S`, and
the comparison with `[[X/G_S]]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.QuotientStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

/-- Remark 95.15.5 (1): the stack in groupoids `[[X/G]]` over `(Sch/S)_fppf`
associated to an algebraic space `X` over `S` and a homomorphism
`G →* Aut X`. -/
@[stacks 0371]
noncomputable abbrev stack {S : Scheme.{u}} {G : Type u} [Group G]
    {X : AlgebraicSpace S} (ρ : G →* Aut X) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  AbstractGroup.stack ρ

/-- The projection of the abstract-group quotient stack is the forgetful functor
to `(Sch/S)_fppf`. -/
theorem stack_p {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
    (ρ : G →* Aut X) : (stack ρ).p = AbstractGroup.forget ρ := sorry

/-- Remark 95.15.5 (2): if the cardinality of `G` is not too large, the constant
sheaf `underline(G)` is represented by the constant group scheme `G_S` on
`(Sch/S)_fppf`. -/
@[stacks 0371]
theorem constantSheaf_represented (S : Scheme.{u}) (G : GrpCat.{u}) :
    IsIsomorphic (AbstractGroup.constantGroupSheaf S G).obj
      (yonedaGrp.obj (ConstantGroup.baseChange S G)) := sorry

/-- Remark 95.15.5 (3): the abstract-group stack `[[X/G]]` is equivalent to the
stack `[[X/G_S]]` associated with the constant group scheme. -/
@[stacks 0371]
noncomputable def equivalent_baseChange {S : Scheme.{u}} {G : Type u} [Group G]
    {X : AlgebraicSpace S} (ρ : G →* Aut X) :
    AbstractGroup.stack ρ ≌ BaseChange.stack ρ :=
  BaseChange.equivalent_baseChange ρ

/-- The comparison equivalence is an equivalence of stacks over `(Sch/S)_fppf`. -/
theorem equivalent_baseChange_hom {S : Scheme.{u}} {G : Type u} [Group G]
    {X : AlgebraicSpace S} (ρ : G →* Aut X) :
    IsEquivalence (equivalent_baseChange ρ).hom := sorry
