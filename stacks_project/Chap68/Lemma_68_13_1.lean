/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_30_5_Flat

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

namespace Surjective

/-- Lemma 68.13.1 (1): Let `S` be a scheme and let `Z` be an algebraic space over
`S`. If `k` is a field and `cover : ofOver (Over.mk σ) ⟶ Z` is a surjective
flat morphism from `Spec (.of k)`, then any morphism
`f : ofOver (Over.mk σ') ⟶ Z` from `Spec (.of k')` with `k'` a field is
surjective. -/
@[stacks 06QV]
theorem of_specField_cover {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : ofOver (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : ofOver (Over.mk σ') ⟶ Z) : Surjective f :=
  sorry

end Surjective

namespace Flat

/-- Lemma 68.13.1 (2): Let `S` be a scheme and let `Z` be an algebraic space over
`S`. If `k` is a field and `cover : ofOver (Over.mk σ) ⟶ Z` is a surjective
flat morphism from `Spec (.of k)`, then any morphism
`f : ofOver (Over.mk σ') ⟶ Z` from `Spec (.of k')` with `k'` a field is
flat. -/
@[stacks 06QV]
theorem of_specField_cover {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : ofOver (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : ofOver (Over.mk σ') ⟶ Z) : Flat f :=
  sorry

end Flat

namespace FieldValuedPoint

/-- If one field-valued point of an algebraic space is a surjective flat
morphism, then the morphism of every field-valued point is surjective. -/
theorem surjective_hom_of_specField_cover {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (cover p : FieldValuedPoint Z) [Surjective cover.hom] [Flat cover.hom] :
    Surjective p.hom :=
  sorry

/-- If one field-valued point of an algebraic space is a surjective flat
morphism, then the morphism of every field-valued point is flat. -/
theorem flat_hom_of_specField_cover {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (cover p : FieldValuedPoint Z) [Surjective cover.hom] [Flat cover.hom] :
    Flat p.hom :=
  sorry

end FieldValuedPoint

end AlgebraicGeometry.AlgebraicSpace
