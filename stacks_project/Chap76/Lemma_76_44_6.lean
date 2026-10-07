module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion
public import stacks_project.Chap76.«76_6_1_2_Comparison»

/-!
# Conormal criterion for quasi-regular immersions of algebraic spaces

An immersion of algebraic spaces is quasi-regular if and only if it is locally
of finite presentation, its conormal sheaf is finite locally free, and the
canonical comparison `ConormalAlgebra.symmetricToTotal` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.44.6: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Then `i` is a quasi-regular immersion if and only if
`i` is locally of finite presentation, the conormal sheaf `Hom.conormalSheaf i`
is finite locally free, and the canonical comparison
`ConormalAlgebra.symmetricToTotal i` is an isomorphism. -/
@[stacks 09RY]
theorem IsQuasiRegularImmersion.iff_locallyOfFinitePresentation_conormal
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    IsQuasiRegularImmersion i ↔
      LocallyOfFinitePresentation i ∧ (Hom.conormalSheaf i).IsFiniteLocallyFree ∧
        IsIso (ConormalAlgebra.symmetricToTotal i) :=
  sorry

/-- A quasi-regular immersion of algebraic spaces is locally of finite
presentation. -/
instance IsQuasiRegularImmersion.locallyOfFinitePresentation
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsQuasiRegularImmersion i] : LocallyOfFinitePresentation i :=
  sorry

/-- The conormal sheaf of a quasi-regular immersion of algebraic spaces is finite
locally free. -/
instance IsQuasiRegularImmersion.isFiniteLocallyFree_conormalSheaf
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsQuasiRegularImmersion i] : (Hom.conormalSheaf i).IsFiniteLocallyFree :=
  sorry

/-- For a quasi-regular immersion of algebraic spaces, the canonical comparison
`ConormalAlgebra.symmetricToTotal i` is an isomorphism. -/
instance IsQuasiRegularImmersion.isIso_symmetricToTotal
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsQuasiRegularImmersion i] : IsIso (ConormalAlgebra.symmetricToTotal i) :=
  sorry

/-- An immersion of algebraic spaces that is locally of finite presentation,
whose conormal sheaf is finite locally free, and for which
`ConormalAlgebra.symmetricToTotal i` is an isomorphism, is a quasi-regular
immersion. -/
theorem IsQuasiRegularImmersion.of_locallyOfFinitePresentation_conormal
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    [LocallyOfFinitePresentation i] [(Hom.conormalSheaf i).IsFiniteLocallyFree]
    [IsIso (ConormalAlgebra.symmetricToTotal i)] :
    IsQuasiRegularImmersion i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
