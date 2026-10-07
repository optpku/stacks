module

public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact

/-!
# Finite coproducts of quasi-compact algebraic spaces

A finite disjoint union of quasi-compact algebraic spaces is again quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.5.3: a finite disjoint union of quasi-compact algebraic spaces is a
quasi-compact algebraic space. -/
@[stacks 040T, instance]
instance instIsQuasiCompact_coproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → AlgebraicSpace S) [∀ i, IsQuasiCompact (X i)] :
    IsQuasiCompact (coproduct X) := sorry

end AlgebraicGeometry.AlgebraicSpace
