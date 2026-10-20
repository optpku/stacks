module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField.Multiplication
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Multiplication
import StacksCheckRecall

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

/- Lemma 79.9.3: composition of a groupoid on a field and the group law of a
group algebraic space over a field are flat and universally open. -/
@[stacks 06E0] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.flat_composition :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
      (σ : Spec (.of k) ⟶ S) [GroupoidAlgebraicSpace.IsOnField G σ],
      AlgebraicSpace.Flat G.c.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.universallyOpen_composition :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
      (σ : Spec (.of k) ⟶ S) [GroupoidAlgebraicSpace.IsOnField G σ],
      AlgebraicSpace.UniversallyOpen G.c.left)

#check (AlgebraicGeometry.GroupAlgebraicSpace.instFlat_mul :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S}
      (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))),
      AlgebraicSpace.Flat (μ[G.X]).left)

#check (AlgebraicGeometry.GroupAlgebraicSpace.instUniversallyOpen_mul :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S}
      (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))),
      AlgebraicSpace.UniversallyOpen (μ[G.X]).left)
