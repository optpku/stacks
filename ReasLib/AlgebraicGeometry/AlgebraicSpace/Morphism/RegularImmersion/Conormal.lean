module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Symmetric

/-!
# Conormal criterion for quasi-regular immersions of algebraic spaces

An immersion of algebraic spaces is quasi-regular if and only if it is locally
of finite presentation, its conormal sheaf is finite locally free, and the
canonical comparison `ConormalAlgebra.symmetricToTotal` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom (conormalSheaf)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An immersion of algebraic spaces over a scheme is quasi-regular if and only
if it is locally of finite presentation, its conormal sheaf is finite locally
free, and the canonical symmetric-to-total comparison is an isomorphism. -/
theorem IsQuasiRegularImmersion.iff_locallyOfFinitePresentation_conormal
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    IsQuasiRegularImmersion i ↔
      LocallyOfFinitePresentation i ∧ (conormalSheaf i).IsFiniteLocallyFree ∧
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
    [IsQuasiRegularImmersion i] : (conormalSheaf i).IsFiniteLocallyFree :=
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
@[instance 100]
theorem IsQuasiRegularImmersion.of_locallyOfFinitePresentation_conormal
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    [LocallyOfFinitePresentation i] [(conormalSheaf i).IsFiniteLocallyFree]
    [IsIso (ConormalAlgebra.symmetricToTotal i)] :
    IsQuasiRegularImmersion i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
