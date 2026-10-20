module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Descent

/-!
# Remark 95.14.6

The source conjectures that `p : G-Principal ⟶ (Sch/S)_fppf` is a stack in
groupoids, up to the small-fiber replacement of Remark 8.4.9. Effective fppf
descent of principal homogeneous spaces reduces the remaining gap to a
set-theoretic size condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupAlgebraicSpace

universe u v

/- Remark 95.14.6 (1): we conjecture that, up to a replacement as in
Remark 8.4.9, the functor `p : G-Principal ⟶ (Sch/S)_fppf` given by
`Principal.forget` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 04UP]
#check (AlgebraicGeometry.GroupAlgebraicSpace.Principal.instIsStackInGroupoids :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B},
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.GroupAlgebraicSpace.Principal.forget G))

/- Fiberwise essential smallness supplies the size condition in
Remark 8.4.9 for the replacement. -/
#check (AlgebraicGeometry.GroupAlgebraicSpace.Principal.fibers_essentiallySmall :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (U : Over S),
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty
        ((AlgebraicGeometry.GroupAlgebraicSpace.Principal.forget G).Fiber U)))

/- Remark 95.14.6 (2): given an fppf covering `{U_i ⟶ U}_{i ∈ I}`, a group
algebraic space `H` over `U`, local principal homogeneous `H_{U_i}`-spaces, and
`H`-equivariant overlap isomorphisms satisfying the cocycle condition, there
exists a global principal homogeneous `H`-space recovering the supplied datum.
The retained hypothesis `[Small.{u} I]` is the size condition of Spaces,
Lemma 65.8.4, as in Bootstrap, Lemma 80.11.8. -/
@[stacks 04UP]
#check
  (AlgebraicGeometry.GroupAlgebraicSpace.Principal.DescentDatum.exists_principalHomogeneous :
    ∀ {U : Scheme.{u}} {I : Type v} [Small.{u} I]
      {Ui : I → Over U} {H : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 U)))}
      (D : AlgebraicGeometry.GroupAlgebraicSpace.Principal.DescentDatum Ui H),
      Nonempty D.Effectiveness)
