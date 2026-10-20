module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldCover
import StacksCheckRecall

/-!
# Field-spectrum morphisms into an algebraic space with a flat surjective field cover

If an algebraic space over a scheme admits one surjective flat morphism from the
spectrum of a field, then every morphism from the spectrum of a field is
surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.13.1: Let S be a scheme. Let Z be an algebraic space over S.
Let k be a field and let Spec(k) → Z be surjective and flat. Then any morphism
Spec(k') → Z where k' is a field is surjective and flat. -/
@[stacks 06QV]
#check (AlgebraicGeometry.AlgebraicSpace.surjective_and_flat_of_specField_cover :
  ∀ {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : ofOver (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : ofOver (Over.mk σ') ⟶ Z), Surjective f ∧ Flat f)

end AlgebraicGeometry.AlgebraicSpace
