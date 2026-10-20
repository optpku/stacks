/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import stacks_project.Chap66.Lemma_66_7_1_EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.7.1 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`P` be a property of schemes which is local in the étale topology. Then there exists a
scheme `U` and a surjective étale morphism `U ⟶ X` with `P U.left` if and only if every
étale morphism `U ⟶ X` from a scheme has `P U.left`. -/
@[stacks 03E8] #check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale_iff_forallEtale :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (X : AlgebraicSpace S), existsSurjectiveEtale P X ↔ forallEtale P X)

/- Lemma 66.7.1 (2): if `X` is representable by a scheme `T` over `S`, the existence of a
surjective étale scheme atlas with property `P` is equivalent to `P T.left`. -/
@[stacks 03E8] #check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale_ofOver :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (T : Over S), existsSurjectiveEtale P (ofOver T) ↔ P T.left)

/- If `T` is a scheme over `S`, then every étale morphism from a scheme to `ofOver T` has
property `P` if and only if `T.left` has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.forallEtale_ofOver :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (T : Over S), forallEtale P (ofOver T) ↔ P T.left)

/- The étale-local atlas criterion transports along an isomorphism to a representable
algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale_iso :
  ∀ {S : Scheme.{u}} (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    {X : AlgebraicSpace S} {T : Over S} (e : X ≅ ofOver T),
    existsSurjectiveEtale P X ↔ P T.left)

end AlgebraicGeometry.AlgebraicSpace
