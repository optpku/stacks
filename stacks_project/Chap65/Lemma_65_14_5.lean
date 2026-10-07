module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Lemma_65_14_3_Relation

/-!
# Finite-group quotients inherit quasi-separatedness and separatedness
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- If `G` is finite and `U ⟶ S` is quasi-separated, then `j = (ofAut ρ).hom` is
quasi-compact. -/
instance instQuasiCompact_hom_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [QuasiSeparated U.hom] : QuasiCompact (ofAut ρ).hom.left := sorry

/-- Lemma 65.14.5 (1): with notation and assumptions as in Lemma 65.14.3, if `G` is finite
and `U ⟶ S` is quasi-separated, then `U/G` is quasi-separated over `S`. -/
@[stacks 02Z4]
theorem quasiCompact_diag_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [QuasiSeparated U.hom] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

/-- If `G` is finite and `U ⟶ S` is separated, then `j = (ofAut ρ).hom` is a closed
immersion. -/
instance instIsClosedImmersion_hom_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [IsSeparated U.hom] : IsClosedImmersion (ofAut ρ).hom.left := sorry

/-- Lemma 65.14.5 (2): with notation and assumptions as in Lemma 65.14.3, if `G` is finite
and `U ⟶ S` is separated, then `U/G` is separated over `S`. -/
@[stacks 02Z4]
theorem isClosedImmersion_diag_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [IsSeparated U.hom] :
    (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) := sorry

end AlgebraicGeometry.Scheme.PreRelation
