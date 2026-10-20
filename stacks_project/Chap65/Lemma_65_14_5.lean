/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FiniteGroupAction
import StacksCheckRecall

/-!
# Finite-group quotients inherit quasi-separatedness and separatedness
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.Scheme.PreRelation

/- Lemma 65.14.5 (1): the quotient by a finite free group action inherits
quasi-separatedness over the base. -/
@[stacks 02Z4] #check (AlgebraicGeometry.Scheme.PreRelation.quasiCompact_diag_ofAut :
  ∀ {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [QuasiSeparated U.hom],
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj))

/- Lemma 65.14.5 (2): the quotient by a finite free group action inherits
separatedness over the base. -/
@[stacks 02Z4] #check (AlgebraicGeometry.Scheme.PreRelation.isClosedImmersion_diag_ofAut :
  ∀ {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [IsSeparated U.hom],
    (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
      (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj))
