/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import stacks_project.Chap66.Lemma_66_7_1

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 66.7.2: let `P` be a property of schemes which is local in the étale topology,
let `S` be a scheme, and let `X` be an algebraic space over `S`. We say `X` has property `P`
if any of the equivalent conditions of Lemma 66.7.1 hold. -/
@[stacks 03E6] #check (AlgebraicGeometry.AlgebraicSpace.hasEtaleLocal :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage],
    AlgebraicSpace S → Prop)

/- If `P` is étale-local, then `X` has property `P` if and only if every étale morphism from a
scheme to `X` has property `P` on the source. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale_iff_forallEtale :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (X : AlgebraicSpace S), hasEtaleLocal P X ↔ forallEtale P X)

/- If `T` is a scheme over `S`, then `ofOver T` has an étale-local scheme property `P` if and
only if `T.left` has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale_ofOver :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (T : Over S), hasEtaleLocal P (ofOver T) ↔ P T.left)

end AlgebraicGeometry.AlgebraicSpace
