module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SiteRestriction
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.80.1: if every local ring of a scheme `S` is strictly henselian, then for
every abelian sheaf `F` on the small étale site the groups `H^i(S_étale, F)` agree
with the cohomology of the restriction of `F` to the small Zariski site. -/
@[stacks 09AX] #check
  (AlgebraicGeometry.Scheme.etaleCohomology_eq_zariski_of_hasStrictlyHenselianStalks :
    ∀ (S : Scheme.{u}) [HasStrictlyHenselianStalks S]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (i : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})],
    IsIsomorphic
      ((Sheaf.functorH S.smallEtaleTopology i).obj F)
      ((Sheaf.functorH S.smallZariskiTopology i).obj
        (((smallZariskiToSmallEtale S).sheafPushforwardContinuous
          AddCommGrpCat.{u} S.smallZariskiTopology S.smallEtaleTopology).obj F)))

end AlgebraicGeometry.Scheme
