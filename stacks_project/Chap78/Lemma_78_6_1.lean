/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

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

/-- Lemma 78.6.1 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is separated if
and only if the identity section `η[G.X].left` is a closed immersion. -/
@[stacks 06P6]
theorem isSeparated_iff_isClosedImmersion_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.Separated G.X.hom ↔ AlgebraicSpace.IsClosedImmersion η[G.X].left :=
  sorry

/-- Lemma 78.6.1 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is quasi-separated
if and only if the identity section `η[G.X].left` is quasi-compact. -/
@[stacks 06P6]
theorem quasiSeparated_iff_quasiCompact_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.QuasiSeparated G.X.hom ↔ AlgebraicSpace.QuasiCompact η[G.X].left :=
  sorry

/-- Lemma 78.6.1 (3): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Then `G.X.hom` is locally
separated if and only if the identity section `η[G.X].left` is an immersion. -/
@[stacks 06P6]
theorem locallySeparated_iff_isImmersion_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    AlgebraicSpace.LocallySeparated G.X.hom ↔ AlgebraicSpace.IsImmersion η[G.X].left :=
  sorry

/-- A group algebraic space with closed identity section has separated structure
morphism. -/
instance instSeparatedOfIsClosedImmersionOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.IsClosedImmersion η[G].left] :
    AlgebraicSpace.Separated G.hom :=
  sorry

/-- A group algebraic space with quasi-compact identity section has quasi-separated
structure morphism. -/
instance instQuasiSeparatedOfQuasiCompactOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.QuasiCompact η[G].left] :
    AlgebraicSpace.QuasiSeparated G.hom :=
  sorry

/-- A group algebraic space with immersion identity section has locally separated
structure morphism. -/
instance instLocallySeparatedOfIsImmersionOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : Over B) [GrpObj G] [AlgebraicSpace.IsImmersion η[G].left] :
    AlgebraicSpace.LocallySeparated G.hom :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
