module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ZeroDimensional
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.80.3: if `S` is affine, every point of `S` is closed, and every
residue field of `S` is separably algebraically closed, then
`H^i(S_étale, F) = 0` for every abelian étale sheaf `F` and every `i > 0`. -/
@[stacks 09AY]
#check (AlgebraicGeometry.Scheme.etaleCohomology_isZero_of_affine_closedPoints_sepClosedResidue :
  ∀ (S : Scheme.{u}) [IsAffine S],
    (∀ x : S, IsClosed ({x} : Set S)) →
    (∀ x : S, IsSepClosed (S.residueField x)) →
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) →
    (i : ℕ) → 0 < i →
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}] →
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] →
    IsZero ((Sheaf.functorH S.smallEtaleTopology i).obj F))

end AlgebraicGeometry.Scheme
