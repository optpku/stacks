module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_13_4

/-!
# Bootstrap-flat representable morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Flat

/-- Lemma 88.13.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. If `f` is representable
by algebraic spaces and flat in the sense of Bootstrap, Definition 80.4.1,
i.e. every scheme Yoneda pullback of `f` is `AlgebraicSpace.Flat`, then `f`
is flat in the sense of Definition 88.13.4. -/
@[stacks 0GCG]
theorem of_relativeAlgebraicSpaces {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f)
    (hflat : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Flat (hf.pullbackHom ξ)) :
    Flat f :=
  sorry

end Flat

end AlgebraicGeometry.FormalAlgebraicSpace
