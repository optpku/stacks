module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category

/-!
# Filtered colimits of coherent submodules

Coherent subobjects of a quasi-coherent module on a Noetherian algebraic stack form a filtered
diagram under inclusion, with the ambient module as its colimit.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory GroupoidsOver
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The coherent subobjects of a module on a locally Noetherian algebraic stack. -/
def coherentSubobjects [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) : Set (Subobject F) :=
  {G | AlgebraicStack.IsCoherent (G : SheafOfModules.{u} (structureSheaf X))}

/-- A subobject belongs to `coherentSubobjects F` exactly when its underlying module is
coherent. -/
@[simp] theorem mem_coherentSubobjects [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) (G : Subobject F) :
    G ∈ coherentSubobjects F ↔ AlgebraicStack.IsCoherent (G : SheafOfModules.{u} (structureSheaf X)) :=
  Iff.rfl

/-- The inclusion diagram of all coherent subobjects of a module. -/
def coherentSubobjectsDiagram [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    (coherentSubobjects F) ⥤ SheafOfModules.{u} (structureSheaf X) where
  obj G := (G.1 : SheafOfModules.{u} (structureSheaf X))
  map f := Subobject.ofLE _ _ f.le
  map_id G := by
    exact Subobject.ofLE_refl G.1
  map_comp f g := by
    exact (Subobject.ofLE_comp_ofLE _ _ _ f.le g.le).symm

/-- The cocone of canonical inclusions from coherent subobjects into the ambient module. -/
def coherentSubobjectsCocone [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    Cocone (coherentSubobjectsDiagram F) where
  pt := F
  ι := {
    app := fun G => G.1.arrow
    naturality := by
      intro G H f
      exact Subobject.ofLE_arrow f.le
  }

/-- The object of the coherent-subobject diagram at an index is its underlying module. -/
@[simp] theorem coherentSubobjectsDiagram_obj [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) (G : coherentSubobjects F) :
    (coherentSubobjectsDiagram F).obj G =
      (G.1 : SheafOfModules.{u} (structureSheaf X)) := rfl

/-- The map of the coherent-subobject diagram is the canonical inclusion map. -/
@[simp] theorem coherentSubobjectsDiagram_map [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X))
    {G H : coherentSubobjects F} (f : G ⟶ H) :
    (coherentSubobjectsDiagram F).map f = Subobject.ofLE G.1 H.1 f.le := rfl

/-- The vertex of the coherent-subobject cocone is the ambient module. -/
@[simp] theorem coherentSubobjectsCocone_pt [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    (coherentSubobjectsCocone F).pt = F := rfl

/-- The cocone component at a coherent subobject is its canonical inclusion. -/
@[simp] theorem coherentSubobjectsCocone_app [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) (G : coherentSubobjects F) :
    (coherentSubobjectsCocone F).ι.app G = G.1.arrow := rfl

/-- On a Noetherian algebraic stack, the coherent subobjects of a quasi-coherent module are
directed by inclusion and have supremum the whole module. -/
theorem coherentSubobjects_isDirectedColimit [IsNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (coherentSubobjects F) ∧
      IsLUB (coherentSubobjects F) (⊤ : Subobject F) :=
  sorry

/-- On a Noetherian algebraic stack, every quasi-coherent module is a small filtered colimit of
coherent modules. -/
theorem isCoherent_ind [IsNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    (coherentModuleProperty X).ind.{u} F :=
  sorry

/-- The coherent-subobject inclusion diagram is filtered and its canonical cocone is a colimit. -/
theorem coherentSubobjects_isFilteredColimit [IsNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    CategoryTheory.IsFiltered (coherentSubobjects F) ∧
      Nonempty (CategoryTheory.Limits.IsColimit (coherentSubobjectsCocone F)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
