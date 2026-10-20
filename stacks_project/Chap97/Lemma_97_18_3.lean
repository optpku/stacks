module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap78.Lemma_78_27_2_TrivialAction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# When the classifying quotient stack is algebraic

The quotient stack of the trivial action of a group algebraic space `G` over an
algebraic space `B` over a scheme `S` is algebraic if and only if `G ⟶ B` is
flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 97.18.3. Let `S` be a scheme and let `B` be an algebraic space over
`S`. Let `G` be a group algebraic space over `B`. Endow `B` with the trivial
action of `G`. Then the quotient stack of `B` by `G` is an algebraic stack if
and only if `G` is flat and locally of finite presentation over `B`. -/
@[stacks 06PL]
theorem isAlgebraicStack_trivialAction_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicStack (ofAction G (trivialAction G)).quotientStack ↔
      AlgebraicSpace.Flat G.X.hom ∧
        AlgebraicSpace.LocallyOfFinitePresentation G.X.hom :=
  sorry

/-- If `G.X.hom` is flat and locally of finite presentation, then the quotient
stack of the trivial `G`-action on `B` is an algebraic stack. -/
instance instAlgebraicStack_trivialAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicStack (ofAction G (trivialAction G)).quotientStack :=
  sorry

/-- If the quotient stack of the trivial `G`-action on `B` is algebraic, then
`G.X.hom` is flat. -/
theorem flat_hom_of_isAlgebraicStack_trivialAction {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (h_algebraic : AlgebraicStack (ofAction G (trivialAction G)).quotientStack) :
    AlgebraicSpace.Flat G.X.hom :=
  sorry

/-- If the quotient stack of the trivial `G`-action on `B` is algebraic, then
`G.X.hom` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_hom_of_isAlgebraicStack_trivialAction
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (h_algebraic : AlgebraicStack (ofAction G (trivialAction G)).quotientStack) :
    AlgebraicSpace.LocallyOfFinitePresentation G.X.hom :=
  sorry

/-- For the trivial `G`-action on `B`, flatness of `G.X.hom` is equivalent to
flatness of the associated action groupoid. -/
theorem flat_hom_iff_flat_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.Flat G.X.hom ↔
      GroupoidAlgebraicSpace.Flat (ofAction G (trivialAction G)) :=
  sorry

/-- For the trivial `G`-action on `B`, local finite presentation of `G.X.hom` is
equivalent to local finite presentation of the associated action groupoid. -/
theorem locallyOfFinitePresentation_hom_iff_ofAction {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.LocallyOfFinitePresentation G.X.hom ↔
      GroupoidAlgebraicSpace.LocallyOfFinitePresentation
        (ofAction G (trivialAction G)) :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
