module

public import Mathlib.CategoryTheory.Presentable.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap103.Lemma_103_13_5_TestSet

/-!
# Hom out of finitely presented modules on qcqs algebraic stacks

On a quasi-compact and quasi-separated algebraic stack, a finitely presented
`𝒪_X`-module is a finitely presentable object of `Mod(𝒪_X)`, so represented Hom
commutes with filtered colimits of arbitrary `𝒪_X`-modules, and likewise after
restriction to `QCoh X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The canonical comparison `colim Hom_X(G, F_i) ⟶ Hom_X(G, colim F_i)`. -/
noncomputable abbrev homComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : RingedSite.ModuleCat.{u} (fppfRingedSite X))
    (F : Λ ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    colimit (F ⋙ coyoneda.obj (op G)) ⟶ (coyoneda.obj (op G)).obj (colimit F) :=
  colimit.post F (coyoneda.obj (op G))

/-- The Hom comparison is determined on each colimit coprojection. -/
theorem homComparison_ι {S : Scheme.{u}} {X : GroupoidsOver S}
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : RingedSite.ModuleCat.{u} (fppfRingedSite X))
    (F : Λ ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] (i : Λ) :
    colimit.ι (F ⋙ coyoneda.obj (op G)) i ≫ homComparison G F =
      (coyoneda.obj (op G)).map (colimit.ι F i) :=
  sorry

/-- On a qcqs algebraic stack, Hom out of a finitely presented `𝒪_X`-module
commutes with a filtered colimit of arbitrary `𝒪_X`-modules. -/
instance homComparison_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : RingedSite.ModuleCat.{u} (fppfRingedSite X)) [G.IsFinitePresentation]
    (F : Λ ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    IsIso (homComparison G F) :=
  sorry

/-- On a qcqs algebraic stack, a finitely presented `𝒪_X`-module is finitely
presentable in `Mod(𝒪_X)`. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    (G : RingedSite.ModuleCat.{u} (fppfRingedSite X)) [G.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver.QCoh

open AlgebraicGeometry.AlgebraicStack

/-- On a qcqs algebraic stack, a finitely presented quasi-coherent `𝒪_X`-module
is finitely presentable in `QCoh X`. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    (G : QCoh X) [G.obj.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
