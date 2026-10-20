/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.CategoryTheory.Sites.Family.Sheaf

/-!
# Sheaf conditions on standard scheme sites

This module specializes the generic family sheaf condition to schemes and
provides the canonical fpqc and Zariski site predicates.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- A scheme presheaf satisfies the sheaf condition for a fixed family exactly
when it is a sheaf for the generated presieve. -/
abbrev satisfiesSheafPropertyForFamily
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) {ι : Type w} {T : Scheme.{u}}
    (family : ι → Scheme.{u}) (map : ∀ i, family i ⟶ T) : Prop :=
  Presheaf.IsSheafForFamily F family map

/-- The scheme-specific fixed-family condition unfolds to the generic
generated-presieve sheaf condition. -/
theorem satisfiesSheafPropertyForFamily_iff
    (F : Scheme.{u}ᵒᵖ ⥤ Type v) {ι : Type w} {T : Scheme.{u}}
    (family : ι → Scheme.{u}) (map : ∀ i, family i ⟶ T) :
    satisfiesSheafPropertyForFamily F family map ↔
      Presieve.IsSheafFor F (Presieve.ofArrows family map) := sorry

/-- A scheme presheaf is an fpqc sheaf when it is a sheaf for the canonical
fpqc Grothendieck topology. -/
abbrev satisfiesFpqcSheafProperty (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  Presheaf.IsSheaf Scheme.fpqcTopology F

/-- The fpqc sheaf condition unfolds to the canonical fpqc topology. -/
theorem satisfiesFpqcSheafProperty_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    satisfiesFpqcSheafProperty F ↔ Presheaf.IsSheaf Scheme.fpqcTopology F := sorry

/-- Every representable presheaf on schemes is a sheaf for the fpqc topology. -/
theorem isSheaf_fpqcTopology_of_isRepresentable
    (P : Scheme.{u}ᵒᵖ ⥤ Type v) [P.IsRepresentable] :
    Presieve.IsSheaf Scheme.fpqcTopology P := sorry

/-- Every representable presheaf on schemes over a fixed scheme is a sheaf for the fpqc topology. -/
theorem isSheaf_fpqcTopology_over_of_isRepresentable
    (S : Scheme.{u}) (P : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v) [P.IsRepresentable] :
    CategoryTheory.Presieve.IsSheaf (Scheme.fpqcTopology.over S) P := by
  exact CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/-- A scheme presheaf is a Zariski sheaf when it is a sheaf for the canonical
big Zariski topology. -/
abbrev satisfiesZariskiSheafProperty (F : Scheme.{u}ᵒᵖ ⥤ Type v) : Prop :=
  Presheaf.IsSheaf Scheme.zariskiTopology F

/-- The Zariski sheaf condition unfolds to the canonical big Zariski topology. -/
theorem satisfiesZariskiSheafProperty_iff (F : Scheme.{u}ᵒᵖ ⥤ Type v) :
    satisfiesZariskiSheafProperty F ↔ Presheaf.IsSheaf Scheme.zariskiTopology F := sorry

end AlgebraicGeometry
