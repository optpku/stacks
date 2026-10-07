module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Subobject.Basic
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap103.Definition_103_17_2_Coh

/-!
# Coherent subobjects of quasi-coherent modules on algebraic stacks

On a Noetherian algebraic stack, every quasi-coherent module is the filtered
colimit of its coherent submodules.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory GroupoidsOver

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

end AlgebraicGeometry.AlgebraicStack
