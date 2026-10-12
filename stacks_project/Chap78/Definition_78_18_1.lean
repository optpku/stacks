/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap78.Definition_78_18_1_Invariant
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U) (W : OpenSubspace U.left) (Z : LocallyClosedSubspace U.left)
variable {T : AlgebraicSpace S} (i : T ⟶ U.left) [Mono i]

/- Definition 78.18.1 (1): an open subspace `W ⊂ U` is `R`-invariant if
`t (s⁻¹(W)) ⊂ W`. -/
@[stacks 044F] #check
  (CategoryTheory.Morphism.IsForwardInvariant P.s.left P.t.left W.ι : Prop)

/- Definition 78.18.1 (2): a locally closed subspace `Z ⊂ U` is `R`-invariant if
`t⁻¹(Z) = s⁻¹(Z)` as locally closed subspaces of `R`. -/
@[stacks 044F] #check
  (CategoryTheory.Morphism.IsPullbackInvariant P.s.left P.t.left Z.ι : Prop)

/- Definition 78.18.1 (3): a monomorphism of algebraic spaces `T ⟶ U` is `R`-invariant
if `T ×_U R` along `t` equals `R ×_U T` along `s` as algebraic spaces over `R`. -/
@[stacks 044F] #check
  (CategoryTheory.Subobject.IsInvariant P.s.left P.t.left (Subobject.mk i) : Prop)

#check
  (CategoryTheory.Subobject.isInvariant_mk_iff P.s.left P.t.left i :
    CategoryTheory.Subobject.IsInvariant P.s.left P.t.left (Subobject.mk i) ↔
      ∃ e : Limits.pullback i P.t.left ≅ Limits.pullback i P.s.left,
        e.hom ≫ Limits.pullback.snd i P.s.left = Limits.pullback.snd i P.t.left)
