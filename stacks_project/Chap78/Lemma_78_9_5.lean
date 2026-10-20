module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PseudoTorsor.Morphism
import StacksCheckRecall

/-!
# Unramified and locally quasi-finite pseudo-torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/- Lemma 78.9.5 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
let `G` be a group algebraic space over `B`, and let `X` be a pseudo `G`-torsor
over `B`. If `G` and `X` are locally of finite type over `B` and `G.X.hom` is
unramified, then `X.X.hom` is unramified. -/
@[stacks 0DSK]
#check (AlgebraicGeometry.GroupAlgebraicSpace.unramified_of_isPseudoTorsor :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} (X : Action G) [Mod.IsPseudoTorsor X]
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.Unramified G.X.hom],
    AlgebraicSpace.Unramified X.X.hom)

/- Lemma 78.9.5 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
let `G` be a group algebraic space over `B`, and let `X` be a pseudo `G`-torsor
over `B`. If `G` and `X` are locally of finite type over `B` and `G.X.hom` is
locally quasi-finite, then `X.X.hom` is locally quasi-finite. -/
@[stacks 0DSK]
#check (AlgebraicGeometry.GroupAlgebraicSpace.locallyQuasiFinite_of_isPseudoTorsor :
  ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B} (X : Action G)
    [Mod.IsPseudoTorsor X] [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.LocallyQuasiFinite G.X.hom],
    AlgebraicSpace.LocallyQuasiFinite X.X.hom)

end AlgebraicGeometry.GroupAlgebraicSpace
