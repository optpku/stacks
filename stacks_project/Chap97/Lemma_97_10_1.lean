/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_10_1_SpacePair
public import stacks_project.Chap97.Lemma_97_10_1_Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) (T : AlgebraicSpace S)

/- Lemma 97.10.1 (1): `Mor_B(Z, X)` is a sheaf on `(Sch/S)_fppf`. -/
@[stacks 05Y3]
#check (functor_isSheaf Z X :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor Z X))

/- Lemma 97.10.1 (2): for an algebraic space `T` over `S`, sheaf morphisms
`T ⟶ Mor_B(Z, X)` correspond canonically to pairs `(a, b)` as in (05Y1). -/
@[stacks 05Y3]
#check (homEquiv Z X T :
    (uliftSheaf T ⟶ homSheaf Z X) ≃ SpacePair Z X T)
