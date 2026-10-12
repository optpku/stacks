/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap76.Lemma_76_52_3_Characterization

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.52.3: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is flat and locally of finite presentation. Let `E` be an object of
`D_QCoh(𝒪_X)`. The following are equivalent: `E` is `Y`-perfect; for every étale scheme
square over `f`, the restriction `E|_U` is `V`-perfect in the sense of
`Scheme.ModuleDerived.IsPerfectRelativeTo`; for some such square with `U ⟶ X` surjective,
`E|_U` is `V`-perfect; and for every such square with `U` and `V` affine, `RΓ(U, E)` is
`𝒪_Y(V)`-perfect. -/
@[stacks 0DKQ]
theorem IsPerfectRelativeTo.tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) :
    List.TFAE [IsPerfectRelativeTo f E, IsPerfectRelativeTo.everyEtaleSquare f E,
      IsPerfectRelativeTo.existsSurjectiveEtaleSquare f E,
      IsPerfectRelativeTo.everyAffineSections f E] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
