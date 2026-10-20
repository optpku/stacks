module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Map.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : IsPullback f i i' g)

/- Lemma 76.6.4 (1): Let `S` be a scheme. In a cartesian square of algebraic spaces
over `S` whose horizontal arrows `i : Z ⟶ X` and `i' : Z' ⟶ X'` are immersions,
the canonical map `ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i` of
Lemma 76.6.3 is surjective. -/
@[stacks 09RT]
#check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.map_isLocallySurjective_of_isPullback sq :
    Sheaf.IsLocallySurjective (ConormalAlgebra.map sq.toCommSq).hom.right)

variable [Flat g]

/- Lemma 76.6.4 (2): If in addition `g : X ⟶ X'` is flat, that same canonical map
is an isomorphism. -/
@[stacks 09RT]
#check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.map_isIso_of_isPullback_of_flat sq :
    IsIso (ConormalAlgebra.map sq.toCommSq :
      ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i))
