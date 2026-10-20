/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InductionSets
import StacksCheckRecall

/-!
# Choosing the collection in the qcqs spaces-étale induction lemma

Remark 75.9.5 records three standard collections `B` to which Lemma 75.9.4
applies: quasi-compact absolutely separated objects, quasi-compact objects with
affine diagonal over the terminal scheme, and the smallest collection generated
by quasi-compact opens of `X` and of affine objects of the site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 75.9.5 (1): if `X` is quasi-compact and separated, the collection of
quasi-compact and separated objects of `X_spaces,étale` contains `X` and
satisfies (1), (2), and (3)(a) of Lemma 75.9.4. -/
@[stacks 08GR] #check
  (AlgebraicGeometry.AlgebraicSpace.qcAbsolutelySeparatedSpacesEtale_spec :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X],
    spacesEtaleSite.self X ∈ qcAbsolutelySeparatedSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelySeparatedSpacesEtale X))

/- Remark 75.9.5 (2): if `X` is quasi-compact with affine diagonal over the
terminal scheme, the collection of quasi-compact objects of `X_spaces,étale`
with affine diagonal over the terminal scheme contains `X` and satisfies (1),
(2), and (3)(a) of Lemma 75.9.4. -/
@[stacks 08GR] #check
  (AlgebraicGeometry.AlgebraicSpace.qcAbsolutelyAffineDiagonalSpacesEtale_spec :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X],
    spacesEtaleSite.self X ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelyAffineDiagonalSpacesEtale X))

/- Remark 75.9.5 (3): if `X` is quasi-compact and quasi-separated, the
smallest collection containing `X` and satisfying (1), (2), and (3)(a) of
Lemma 75.9.4 is the set of quasi-compact open subspaces of `X` and of affine
objects of `X_spaces,étale`. -/
@[stacks 08GR] #check
  (AlgebraicGeometry.AlgebraicSpace.qcqsGeneratedSpacesEtale_spec :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
    qcqsGeneratedSpacesEtale X =
      sInf {B | spacesEtaleSite.self X ∈ B ∧ QcqsSpacesEtaleInductionSet B})

/- The separated collection yields induction on quasi-compact absolutely separated objects. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.qcqsSpacesEtale_induction_of_absolutelySeparated :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X]
    (P : spacesEtaleSite X → Prop)
    (h_affine : ∀ (W : spacesEtaleSite X) [IsAffine W.left], P W)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) [IsQuasiCompact W.left] [IsAbsolutelySeparated W.left],
    P W)

end AlgebraicGeometry.AlgebraicSpace
