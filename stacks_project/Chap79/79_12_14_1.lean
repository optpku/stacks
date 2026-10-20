module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.SectionPair
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits

universe u

/- 79.12.14.1: For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a section `σ : Y ⟶ X` of `f`, and for an algebraic space or a scheme `T`
over `S`, a variant pair `(a, Z)` consists of a morphism `a : T ⟶ Y` over `S`
together with an open subspace `Z : OpenSubspace (pullback a f)` of `T ×_Y X`
such that `IsFinite (Z.ι ≫ pullback.fst a f)`, i.e. `pr₀|_Z : Z ⟶ T` is finite,
and the graph `(1_T, σ ∘ a) : T ⟶ T ×_Y X` given by
`FinitePart.sectionGraph a f σ hσ` factors through `Z`. -/
@[stacks 04RQ] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
