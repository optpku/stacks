module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Composition and group law over a field

In Situation 79.9.2 the composition of a groupoid in algebraic spaces on a field
is flat and universally open. In Situation 79.9.1 the group law of a group
algebraic space over a field is flat and universally open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 79.9.3 (1): in Situation 79.9.2 the composition morphism
`G.c : pullback G.s G.t ⟶ G.R` is flat. -/
@[stacks 06E0]
theorem flat_composition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.Flat G.c.left := sorry

/-- Lemma 79.9.3 (2): in Situation 79.9.2 the composition morphism
`G.c : pullback G.s G.t ⟶ G.R` is universally open. -/
@[stacks 06E0]
theorem universallyOpen_composition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.UniversallyOpen G.c.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.9.3 (3): in Situation 79.9.1 the group law
`μ[G.X] : G.X ⊗ G.X ⟶ G.X` is flat. -/
@[stacks 06E0, instance]
instance instFlat_mul {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.Flat (μ[G.X]).left := sorry

/-- Lemma 79.9.3 (4): in Situation 79.9.1 the group law
`μ[G.X] : G.X ⊗ G.X ⟶ G.X` is universally open. -/
@[stacks 06E0, instance]
instance instUniversallyOpen_mul {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.UniversallyOpen (μ[G.X]).left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
