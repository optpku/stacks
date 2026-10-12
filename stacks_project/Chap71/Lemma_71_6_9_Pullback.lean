/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap71.Definition_71_6_1_LocallyPrincipal

/-!
# Pullbacks of locally principal closed subspaces

Local principality of a closed immersion of algebraic spaces is stable under
arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipalClosedSubspace

/-- Local principality of a closed immersion of algebraic spaces is preserved by
the first leg of an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {P X' X Z : AlgebraicSpace S}
    {f : X' ⟶ X} {i : Z ⟶ X} {p : P ⟶ X'} {q : P ⟶ Z}
    (sq : IsPullback p q f i) [IsLocallyPrincipalClosedSubspace i] :
    IsLocallyPrincipalClosedSubspace p :=
  sorry

/-- The inverse-image inclusion of a locally principal closed subspace along a
morphism of algebraic spaces is locally principal. -/
instance inverseImageι {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyPrincipalClosedSubspace i] :
    IsLocallyPrincipalClosedSubspace
      (AlgebraicGeometry.AlgebraicSpace.inverseImageι f i) :=
  sorry

/-- The first projection from the pullback of a locally principal closed immersion
of algebraic spaces is locally principal. -/
instance pullback_fst {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyPrincipalClosedSubspace i] :
    IsLocallyPrincipalClosedSubspace (pullback.fst f i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipalClosedSubspace
