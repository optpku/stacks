module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Separation

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open MonoidalCategory MonObj

universe u

/- Lemma 39.6.1 (1): The structure morphism of a group scheme is separated if and only if
its identity section is a closed immersion. -/
@[stacks 047G] #check
  (AlgebraicGeometry.GroupScheme.isSeparated_iff_isClosedImmersion_one :
    {S : AlgebraicGeometry.Scheme.{u}} → (G : Grp (Over S)) →
      AlgebraicGeometry.IsSeparated G.X.hom ↔
        AlgebraicGeometry.IsClosedImmersion η[G.X].left)

/- Lemma 39.6.1 (2): The structure morphism of a group scheme is quasi-separated if and only if
its identity section is quasi-compact. -/
@[stacks 047G] #check
  (AlgebraicGeometry.GroupScheme.quasiSeparated_iff_quasiCompact_one :
    {S : AlgebraicGeometry.Scheme.{u}} → (G : Grp (Over S)) →
      AlgebraicGeometry.QuasiSeparated G.X.hom ↔
        AlgebraicGeometry.QuasiCompact η[G.X].left)
