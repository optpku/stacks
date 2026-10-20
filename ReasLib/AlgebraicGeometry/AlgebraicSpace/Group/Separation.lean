/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Separation properties of group algebraic spaces

The structure morphism of a group algebraic space is separated (resp.
quasi-separated, resp. locally separated) if and only if the identity
section is a closed immersion (resp. quasi-compact, resp. an immersion).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The structure morphism of a group algebraic space is separated if and only if its
identity section is a closed immersion. -/
theorem isSeparated_iff_isClosedImmersion_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.Separated G.X.hom ↔ AlgebraicSpace.IsClosedImmersion η[G.X].left :=
  sorry

/-- The structure morphism of a group algebraic space is quasi-separated if and only if its
identity section is quasi-compact. -/
theorem quasiSeparated_iff_quasiCompact_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.X.hom ↔ AlgebraicSpace.QuasiCompact η[G.X].left :=
  sorry

/-- The structure morphism of a group algebraic space is locally separated if and only if its
identity section is an immersion. -/
theorem locallySeparated_iff_isImmersion_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.X.hom ↔ AlgebraicSpace.IsImmersion η[G.X].left :=
  sorry

/-- A group algebraic space with closed identity section has separated structure
morphism. -/
instance instSeparatedOfIsClosedImmersionOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.IsClosedImmersion η[G].left] :
    AlgebraicSpace.Separated G.hom :=
  (isSeparated_iff_isClosedImmersion_one (Grp.mk G)).2 inferInstance

/-- A group algebraic space with quasi-compact identity section has quasi-separated
structure morphism. -/
instance instQuasiSeparatedOfQuasiCompactOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.QuasiCompact η[G].left] :
    AlgebraicSpace.QuasiSeparated G.hom :=
  (quasiSeparated_iff_quasiCompact_one (Grp.mk G)).2 inferInstance

/-- A group algebraic space with immersion identity section has locally separated
structure morphism. -/
instance instLocallySeparatedOfIsImmersionOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.IsImmersion η[G].left] :
    AlgebraicSpace.LocallySeparated G.hom :=
  (locallySeparated_iff_isImmersion_one (Grp.mk G)).2 inferInstance

end AlgebraicGeometry.GroupAlgebraicSpace
