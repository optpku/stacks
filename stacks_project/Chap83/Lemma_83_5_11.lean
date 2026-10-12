/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap83.Definition_83_4_1_Invariant
public import stacks_project.Chap83.Definition_83_5_8_Invariant

/-!
# Set-theoretic invariance implies invariance when reduced and locally separated
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Lemma 83.5.11: in the situation of Definition 83.5.8, a morphism `φ : U ⟶ X`
of algebraic spaces over `B` that is set-theoretically `R`-invariant is `R`-invariant
if `R` is reduced and `X` is locally separated over `B`. -/
@[stacks 048Y]
theorem isInvariant_of_isSetTheoreticallyInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
    [AlgebraicSpace.IsReduced P.left.left] {φ : U ⟶ X}
    (hφ : P.IsSetTheoreticallyInvariant φ) : P.IsInvariant φ := sorry

/-- Under reducedness of `R` and local separatedness of `X` over `B`, `R`-invariance of
`φ` is equivalent to set-theoretic `R`-invariance. -/
theorem isInvariant_iff_isSetTheoreticallyInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
    [AlgebraicSpace.IsReduced P.left.left] (φ : U ⟶ X) :
    P.IsInvariant φ ↔ P.IsSetTheoreticallyInvariant φ := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
