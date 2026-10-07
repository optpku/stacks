module

public import Mathlib.CategoryTheory.Presentable.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap69.Lemma_69_5_3_TestSet

/-!
# Hom out of finitely presented modules on qcqs algebraic spaces

On a quasi-compact and quasi-separated algebraic space, a finitely presented `𝒪_X`-module
is a finitely presentable object of `X.Modules`, so represented Hom commutes with filtered
colimits of arbitrary `𝒪_X`-modules, and likewise after restriction to `QCoh X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- The canonical comparison `colim Hom_X(G, F_i) ⟶ Hom_X(G, colim F_i)`. -/
noncomputable abbrev homComparison {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : X.Modules) (F : Λ ⥤ X.Modules)
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    colimit (F ⋙ coyoneda.obj (op G)) ⟶ (coyoneda.obj (op G)).obj (colimit F) :=
  colimit.post F (coyoneda.obj (op G))

/-- The Hom comparison is determined on each colimit coprojection. -/
theorem homComparison_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : X.Modules) (F : Λ ⥤ X.Modules)
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] (i : Λ) :
    colimit.ι (F ⋙ coyoneda.obj (op G)) i ≫ homComparison G F =
      (coyoneda.obj (op G)).map (colimit.ι F i) :=
  sorry

/-- On a qcqs algebraic space, Hom out of a finitely presented `𝒪_X`-module commutes with a
filtered colimit of arbitrary `𝒪_X`-modules. -/
instance homComparison_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : X.Modules) [G.IsFinitePresentation] (F : Λ ⥤ X.Modules)
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    IsIso (homComparison G F) :=
  sorry

/-- On a qcqs algebraic space, a finitely presented `𝒪_X`-module is finitely presentable in
`X.Modules`. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G : X.Modules) [G.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end Modules

namespace QCoh

/-- On a qcqs algebraic space, a finitely presented quasi-coherent `𝒪_X`-module is finitely
presentable in `QCoh X`. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G : QCoh X) [G.obj.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
