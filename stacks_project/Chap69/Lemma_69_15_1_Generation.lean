/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Coherent subobjects of quasi-coherent modules

On a Noetherian algebraic space, every quasi-coherent module is the filtered
colimit of its coherent submodules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The coherent subobjects of a module on a locally Noetherian algebraic space. -/
def coherentSubobjects [IsLocallyNoetherian X] (F : X.Modules) : Set (Subobject F) :=
  {G | ((G : X.Modules)).IsCoherent}

/-- A subobject belongs to `coherentSubobjects F` exactly when its underlying module is
coherent. -/
@[simp] theorem mem_coherentSubobjects [IsLocallyNoetherian X] (F : X.Modules)
    (G : Subobject F) :
    G ∈ coherentSubobjects F ↔ ((G : X.Modules)).IsCoherent :=
  Iff.rfl

/-- On a Noetherian algebraic space, the coherent subobjects of a quasi-coherent module are
directed by inclusion and have supremum the whole module. -/
theorem coherentSubobjects_isDirectedColimit [IsNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (coherentSubobjects F) ∧
      IsLUB (coherentSubobjects F) (⊤ : Subobject F) :=
  sorry

/-- On a Noetherian algebraic space, every quasi-coherent module is a small filtered colimit of
coherent modules. -/
theorem isCoherent_ind [IsNoetherian X] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isCoherent (structureSheaf X)).ind.{u} F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
