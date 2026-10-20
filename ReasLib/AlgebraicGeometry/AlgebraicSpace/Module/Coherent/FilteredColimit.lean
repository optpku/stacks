/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Filtered colimits of coherent submodules

Coherent subobjects of a quasi-coherent module on a Noetherian algebraic space form a filtered
diagram under inclusion, with the ambient module as its colimit.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- The coherent subobjects and their canonical inclusion diagram. -/

/-- The coherent subobjects of a module on a locally Noetherian algebraic space. -/
def coherentSubobjects [IsLocallyNoetherian X] (F : X.Modules) : Set (Subobject F) :=
  {G | ((G : X.Modules)).IsCoherent}

/-- A coherent subobject is characterized by coherence of its underlying module. -/
@[simp] theorem mem_coherentSubobjects [IsLocallyNoetherian X] (F : X.Modules)
    (G : Subobject F) :
    G ∈ coherentSubobjects F ↔ ((G : X.Modules)).IsCoherent :=
  Iff.rfl

/-- The inclusion diagram of all coherent subobjects of a module. -/
def coherentSubobjectsDiagram [IsLocallyNoetherian X] (F : X.Modules) :
    (coherentSubobjects F) ⥤ X.Modules where
  obj G := (G.1 : X.Modules)
  map f := Subobject.ofLE _ _ f.le
  map_id G := by
    exact Subobject.ofLE_refl G.1
  map_comp f g := by
    exact (Subobject.ofLE_comp_ofLE _ _ _ f.le g.le).symm

/-- The cocone of canonical inclusions from coherent subobjects into the ambient module. -/
def coherentSubobjectsCocone [IsLocallyNoetherian X] (F : X.Modules) :
    Cocone (coherentSubobjectsDiagram F) where
  pt := F
  ι := {
    app := fun G => G.1.arrow
    naturality := by
      intro G H f
      exact Subobject.ofLE_arrow f.le
  }

/-- The object of the coherent-subobject diagram at an index is its underlying module. -/
@[simp] theorem coherentSubobjectsDiagram_obj [IsLocallyNoetherian X] (F : X.Modules)
    (G : coherentSubobjects F) :
    (coherentSubobjectsDiagram F).obj G = (G.1 : X.Modules) := rfl

/-- The map of the coherent-subobject diagram is the canonical inclusion map. -/
@[simp] theorem coherentSubobjectsDiagram_map [IsLocallyNoetherian X] (F : X.Modules)
    {G H : coherentSubobjects F} (f : G ⟶ H) :
    (coherentSubobjectsDiagram F).map f = Subobject.ofLE G.1 H.1 f.le := rfl

/-- The vertex of the coherent-subobject cocone is the ambient module. -/
@[simp] theorem coherentSubobjectsCocone_pt [IsLocallyNoetherian X] (F : X.Modules) :
    (coherentSubobjectsCocone F).pt = F := rfl

/-- The cocone component at a coherent subobject is its canonical inclusion. -/
@[simp] theorem coherentSubobjectsCocone_app [IsLocallyNoetherian X] (F : X.Modules)
    (G : coherentSubobjects F) :
    (coherentSubobjectsCocone F).ι.app G = G.1.arrow := rfl

/-- Coherent subobjects are directed and generate the ambient quasi-coherent module. -/
theorem coherentSubobjects_isDirectedColimit [IsNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (coherentSubobjects F) ∧
      IsLUB (coherentSubobjects F) (⊤ : Subobject F) :=
  sorry

/-- Every quasi-coherent module sheaf on a Noetherian algebraic space admits a small filtered
presentation by coherent module sheaves. -/
theorem isCoherent_ind [IsNoetherian X] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isCoherent (structureSheaf X)).ind.{u} F :=
  sorry

/-- The coherent-subobject inclusion diagram is filtered and its canonical cocone is a colimit. -/
theorem coherentSubobjects_isFilteredColimit
    [IsNoetherian X] (F : X.Modules) [F.IsQuasicoherent] :
    CategoryTheory.IsFiltered (coherentSubobjects F) ∧
      Nonempty (CategoryTheory.Limits.IsColimit (coherentSubobjectsCocone F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
