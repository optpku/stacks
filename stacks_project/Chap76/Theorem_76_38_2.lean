/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_18_7_Blowup

/-!
# Flattening modules by admissible blowups of algebraic spaces

A finite-type quasicoherent module on a quasi-compact algebraic space locally of
finite presentation over a qcqs algebraic space, which is finitely presented and
flat over a quasi-compact open of the base, becomes finitely presented and flat
after a `U`-admissible blowup, on the strict transform.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 76.38.2: Let `S` be a scheme. Let `B` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `X` be an algebraic space over `B`.
Let `F` be a quasi-coherent module on `X`. Let `U ⊂ B` be a quasi-compact open
subspace. Assume `X` is quasi-compact, `X` is locally of finite presentation over
`B`, `F` is a module of finite type, `F_U` is of finite presentation, and `F_U` is
flat over `U`. Then there exists a `U`-admissible blowup `B' ⟶ B` such that the
strict transform `F'` of `F` is an `𝒪_{X ×_B B'}`-module of finite presentation
and flat over `B'`. -/
@[stacks 087C]
theorem exists_isAdmissibleBlowup_flattening
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B] [IsQuasiCompact X]
    (f : X ⟶ B) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [((Modules.pullback (pullback.fst f U.ι)).obj F).IsFinitePresentation]
    (h_flat : Modules.flatOver
      ((Modules.pullback (pullback.fst f U.ι)).obj F) (pullback.snd f U.ι)) :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        let F' := strictTransformModule b (Z.inverseImage b) f F
        F'.IsFinitePresentation ∧ Modules.flatOver F' (pullback.snd f b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
