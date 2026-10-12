/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap94.Definition_94_19_3_BaseChange

/-!
# Change of base scheme for relative separation axioms

The properties of being quasi-DM, quasi-separated, or separated over a scheme
are stable under change of base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsQuasiDMOver

/-- Lemma 101.4.6 (1): Being quasi-DM over a scheme, in the sense of
Definition 101.4.2, is stable under change of base scheme. If `X'` is
quasi-DM over `S'`, then `baseChange g X'` of Definition 94.19.3 is
quasi-DM over `S`. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsQuasiDMOver X'] :
    IsQuasiDMOver (baseChange g X') :=
  sorry

end IsQuasiDMOver

namespace IsQuasiSeparatedOver

/-- Lemma 101.4.6 (2): Being quasi-separated over a scheme, in the sense of
Definition 101.4.2, is stable under change of base scheme. If `X'` is
quasi-separated over `S'`, then `baseChange g X'` of Definition 94.19.3 is
quasi-separated over `S`. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsQuasiSeparatedOver X'] :
    IsQuasiSeparatedOver (baseChange g X') :=
  sorry

end IsQuasiSeparatedOver

namespace IsSeparatedOver

/-- Lemma 101.4.6 (3): Being separated over a scheme, in the sense of
Definition 101.4.2, is stable under change of base scheme. If `X'` is
separated over `S'`, then `baseChange g X'` of Definition 94.19.3 is
separated over `S`. -/
@[stacks 050G]
instance of_baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] [IsSeparatedOver X'] :
    IsSeparatedOver (baseChange g X') :=
  sorry

end IsSeparatedOver

end AlgebraicGeometry.AlgebraicStack
