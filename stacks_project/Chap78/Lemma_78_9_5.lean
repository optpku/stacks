module

public import stacks_project.Chap78.Definition_78_8_1_Action
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Unramified and locally quasi-finite pseudo-torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 78.9.5 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
let `G` be a group algebraic space over `B`, and let `X` be a pseudo `G`-torsor
over `B`. If `G` and `X` are locally of finite type over `B` and `G.X.hom` is
unramified, then `X.X.hom` is unramified. -/
@[stacks 0DSK]
instance unramified_of_isPseudoTorsor {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} (X : Action G) [Mod.IsPseudoTorsor X]
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.Unramified G.X.hom] :
    AlgebraicSpace.Unramified X.X.hom := sorry

/-- Lemma 78.9.5 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
let `G` be a group algebraic space over `B`, and let `X` be a pseudo `G`-torsor
over `B`. If `G` and `X` are locally of finite type over `B` and `G.X.hom` is
locally quasi-finite, then `X.X.hom` is locally quasi-finite. -/
@[stacks 0DSK]
instance locallyQuasiFinite_of_isPseudoTorsor {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B} (X : Action G)
    [Mod.IsPseudoTorsor X] [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    [AlgebraicSpace.LocallyOfFiniteType X.X.hom]
    [AlgebraicSpace.LocallyQuasiFinite G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite X.X.hom := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
