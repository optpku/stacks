/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Lemma_79_14_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section

/-!
# The finite part of a groupoid in algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Source compatibility of the canonical morphism `finitePartHom G`. -/
theorem finitePartHom_source (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    (finitePart G).s ≫ (finitePartHom G).obj = (finitePartHom G).arrow ≫ G.s := sorry

/-- Lemma 79.14.1 (1): the object map `g : U' ⟶ U` of the canonical morphism is
identified with `(R_s / U, e)_fin ⟶ U`. -/
@[stacks 04RU]
theorem finitePartHom_obj (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    (finitePartHom G).obj.left =
      FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G) := sorry

/-- Lemma 79.14.1 (2): `univι G` is an open immersion into
`pullback (finitePartHom G).obj.left G.s.left`. -/
@[stacks 04RU, instance]
instance isOpenImmersion_univι (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsOpenImmersion (univι G) := sorry

/-- Lemma 79.14.1 (3): `univι G` is a closed immersion into
`pullback (finitePartHom G).obj.left G.s.left`. -/
@[stacks 04RU, instance]
instance isClosedImmersion_univι (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsClosedImmersion (univι G) := sorry

/-- Lemma 79.14.1 (4): the projection `Z_univ ⟶ U'` is finite. -/
@[stacks 04RU, instance]
instance isFinite_univPr (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsFinite
      (univι G ≫ pullback.fst (finitePartHom G).obj.left G.s.left) := sorry

/-- Lemma 79.14.1 (5): `Z_univ` contains the base change of the unit `e`, and is
the universal such family: an arrow `z` through a with-section pair `p` factors
through `p.Z` if and only if the corresponding point of
`pullback (finitePartHom G).obj.left G.s.left` factors through `univι G`. -/
@[stacks 04RU]
theorem finitePartHom_univ (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    unitLeft G ≫ univι G = unitBaseChange G ∧
      ∀ {T : Over S}
        (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
        (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a),
        factorsThroughOpen G p z ↔
          factorsThroughUnivι G (univPoint G p z hz) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
