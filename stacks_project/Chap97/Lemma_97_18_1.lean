module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap78.Lemma_78_17_1_Restriction
public import stacks_project.Chap78.Lemma_78_19_7_Saturation
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# When a quotient stack is algebraic

The quotient stack `[U / R]` of a groupoid in algebraic spaces over an
algebraic space `B` over a scheme `S` is algebraic if and only if some
restriction along `g : U' ⟶ U` has saturation morphism a surjection of
fppf sheaves and source and target flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 97.18.1: let `S` be a scheme and let `B` be an algebraic space over
`S`. Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`. The
quotient stack `[U / R]` is an algebraic stack if and only if there exists a
morphism of algebraic spaces `g : U' ⟶ U` such that the composition
`U' ×_{g, U, t} R ⟶ R ⟶ U` via `s` is a surjection of sheaves, and the
morphisms `s', t' : R' ⟶ U'` are flat and locally of finite presentation,
where `(U', R', s', t', c')` is the restriction of `(U, R, s, t, c)` via `g`.
Formalized for a groupoid `G` in algebraic spaces over an algebraic space `B`
over `S`, with `[U / R]` as `G.quotientStack`, the restriction as
`G.pullback g`, the saturation composite as `G.saturationMap g`, sheaf
surjection as `Presheaf.IsLocallySurjective` on `Scheme.fppfTopology.over S`,
and `s', t'` flat and locally of finite presentation as `Flat (G.pullback g)`
and `LocallyOfFinitePresentation (G.pullback g)`. -/
@[stacks 06PJ]
theorem isAlgebraicStack_quotientStack_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicStack G.quotientStack ↔
      ∃ (U' : Over B) (g : U' ⟶ G.U),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (G.saturationMap g).left ∧
          Flat (G.pullback g) ∧ LocallyOfFinitePresentation (G.pullback g) :=
  sorry

/-- If a restriction `g : U' ⟶ G.U` has saturation morphism a surjection of
fppf sheaves and the restricted groupoid is flat and locally of finite
presentation, then `G.quotientStack` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_pullback {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    (h_sat : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (G.saturationMap g).left)
    [Flat (G.pullback g)] [LocallyOfFinitePresentation (G.pullback g)] :
    AlgebraicStack G.quotientStack :=
  sorry

/-- If `G.quotientStack` is an algebraic stack, then there exists a restriction
`g : U' ⟶ G.U` whose saturation morphism is a surjection of fppf sheaves and
whose restricted groupoid is flat and locally of finite presentation. -/
theorem exists_pullback_of_isAlgebraicStack_quotientStack {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicStack G.quotientStack] :
    ∃ (U' : Over B) (g : U' ⟶ G.U),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (G.saturationMap g).left ∧
        Flat (G.pullback g) ∧ LocallyOfFinitePresentation (G.pullback g) :=
  sorry

/-- Source-facing expansion of `isAlgebraicStack_quotientStack_iff`: the
restricted source and target `s', t'` are flat and locally of finite
presentation as morphisms of algebraic spaces. -/
theorem isAlgebraicStack_quotientStack_iff_spec {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicStack G.quotientStack ↔
      ∃ (U' : Over B) (g : U' ⟶ G.U),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (G.saturationMap g).left ∧
          AlgebraicSpace.Flat (G.pullback g).s.left ∧
            AlgebraicSpace.Flat (G.pullback g).t.left ∧
              AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left ∧
                AlgebraicSpace.LocallyOfFinitePresentation
                  (G.pullback g).t.left :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
