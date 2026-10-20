module

public import Mathlib.CategoryTheory.Presentable.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FppfSite.QuasiCompact

/-!
# Finitely presented modules on quasi-compact and quasi-separated algebraic stacks

Hom from a finitely presented module sheaf commutes with filtered colimits of
arbitrary module sheaves, and with filtered colimits of quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- On a quasi-compact and quasi-separated algebraic stack, a finitely presented
module sheaf is finitely presentable in the category of all module sheaves. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    (G : SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
    [G.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

/-- On a quasi-compact and quasi-separated algebraic stack, the canonical
comparison from the filtered colimit of Hom sets out of a finitely presented
module sheaf to Hom into the colimit is an isomorphism. -/
instance homComparison_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
    [G.IsFinitePresentation]
    (F : Λ ⥤ SheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X))
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    IsIso (colimit.post F (coyoneda.obj (op G))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver.QCoh

open AlgebraicGeometry.AlgebraicStack

/-- On a quasi-compact and quasi-separated algebraic stack, a finitely presented
quasi-coherent module is finitely presentable in the category of quasi-coherent
modules. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    (G : QCoh X) [G.obj.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
