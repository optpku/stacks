module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.NormalCone
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : IsPullback f i i' g)

/- Lemma 76.5.5 (1): Let `S` be a scheme. In a cartesian square of algebraic spaces
over `S` whose horizontal arrows `i : Z ⟶ X` and `i' : Z' ⟶ X'` are immersions,
the canonical map `f^* C_{Z'/X'} ⟶ C_{Z/X}` of Lemma 76.5.3 is surjective. -/
@[stacks 04CQ]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_epi_of_isPullback sq :
    Epi (Hom.Conormal.map sq.toCommSq))

variable [Flat g]

/- Lemma 76.5.5 (2): If in addition `g : X ⟶ X'` is flat, that same canonical map
is an isomorphism. -/
@[stacks 04CQ]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map_isIso_of_isPullback_of_flat sq :
    IsIso (Hom.Conormal.map sq.toCommSq))
