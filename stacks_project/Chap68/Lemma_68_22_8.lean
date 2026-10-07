module

public import stacks_project.Chap68.Definition_68_22_1_Birational
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap66.Lemma_66_25_4_Normal

/-!
# Integral birational morphisms of decent algebraic spaces with normal target

An integral birational morphism of decent algebraic spaces with finitely many
irreducible components is an isomorphism when the target is normal and the
source is reduced.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- Lemma 68.22.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `X` and `Y` are decent and have finitely many
irreducible components, `f` is integral and birational, `Y` is normal, and `X`
is reduced. Then `f` is an isomorphism. -/
@[stacks 0B4E]
theorem isIso_of_isIntegralHom_of_isNormal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    [IsReduced X] [IsNormal Y] (f : X ⟶ Y) [IsBirational f] [IsIntegralHom f] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational
