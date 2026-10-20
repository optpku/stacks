module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction.Separation
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

/-!
# Separation properties of finite group quotient sheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The fppf quotient sheaf of a finite residue-field free group action on a
quasi-separated scheme over the base has relatively quasi-compact diagonal. -/
@[stacks 02Z4]
theorem quasiCompact_diag_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [QuasiSeparated U.hom] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- The fppf quotient sheaf of a finite residue-field free group action on a separated
scheme over the base has diagonal relatively a closed immersion. -/
@[stacks 02Z4]
theorem isClosedImmersion_diag_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [IsSeparated U.hom] :
    (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

end AlgebraicGeometry.Scheme.PreRelation
