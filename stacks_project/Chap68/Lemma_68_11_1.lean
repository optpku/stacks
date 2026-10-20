/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.11.1 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`.
The assignment sending a monomorphism `Spec(k) ⟶ X`, with `k` a field, to its
class in `|X|` is always injective on isomorphism classes: monomorphic
representatives of the same point are uniquely isomorphic. -/
@[stacks 03K4] #check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_iso_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
      [Mono p.hom] [Mono q.hom],
      Points.mk p = Points.mk q →
        Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q))

/- Lemma 68.11.1 (2): let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. Every point of `|X|` arises from a monomorphism `Spec(k) ⟶ X` with
`k` a field. The canonical result additionally supplies quasi-compactness,
hence proves the required surjectivity. Together with unique isomorphism of
monomorphic representatives, this gives bijectivity on isomorphism classes. -/
@[stacks 03K4] #check
  (AlgebraicGeometry.AlgebraicSpace.IsDecent.exists_quasiCompact_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
      ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x)
