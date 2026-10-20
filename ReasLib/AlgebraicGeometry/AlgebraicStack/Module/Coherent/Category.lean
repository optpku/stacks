module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent

/-!
# The category of coherent modules on a locally Noetherian algebraic stack

Coherent modules form the full subcategory of module sheaves that are finitely
presented on the inherited fppf ringed site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The object property of coherent `𝒪_X`-modules on a locally Noetherian
algebraic stack. -/
abbrev coherentModuleProperty {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    ObjectProperty (SheafOfModules.{u} (structureSheaf X)) :=
  AlgebraicStack.IsCoherent

/-- The coherent module object property is the stack coherence predicate. -/
theorem coherentModuleProperty_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    coherentModuleProperty X = AlgebraicStack.IsCoherent :=
  rfl

/-- A module sheaf on a locally Noetherian algebraic stack lies in
`coherentModuleProperty X` if and only if it is coherent. -/
theorem mem_coherentModuleProperty_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    coherentModuleProperty X F ↔ AlgebraicStack.IsCoherent F :=
  Iff.rfl

/-- The category `Coh(𝒪_X)` of coherent modules on a locally Noetherian
algebraic stack. -/
abbrev Coh {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :=
  (coherentModuleProperty X).FullSubcategory

namespace Coh

/-- The inclusion of coherent modules into all `𝒪_X`-modules. -/
abbrev inclusion {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    Coh X ⥤ SheafOfModules.{u} (structureSheaf X) :=
  (coherentModuleProperty X).ι

end Coh

end AlgebraicGeometry.AlgebraicStack
