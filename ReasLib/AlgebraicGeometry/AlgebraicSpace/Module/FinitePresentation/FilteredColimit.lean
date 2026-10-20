/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.QuasiCompact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Filtered colimits of finitely presented modules

If `f : X ⟶ Y` is an affine morphism of algebraic spaces and `Y` is Noetherian, every
quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely presented modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finitely presented module sheaf on a qcqs algebraic space is finitely presentable. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G : X.Modules) [G.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

/-- The canonical Hom comparison for a filtered diagram of module sheaves is an isomorphism. -/
instance homComparison_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {Λ : Type (u + 1)} [SmallCategory Λ] [IsFiltered Λ]
    (G : X.Modules) [G.IsFinitePresentation] (F : Λ ⥤ X.Modules)
    [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op G))] :
    IsIso (colimit.post F (coyoneda.obj (op G))) :=
  sorry

/-- If `f : X ⟶ Y` is an affine morphism of algebraic spaces over a scheme `S` and `Y` is
Noetherian, then every quasi-coherent `𝒪_X`-module is a small filtered colimit of finitely
presented `𝒪_X`-modules. -/
theorem isFinitePresentation_ind {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [IsNoetherian Y] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- A finitely presented quasi-coherent module on a qcqs algebraic space is finitely presentable. -/
instance isFinitelyPresentable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (G : QCoh X) [G.obj.IsFinitePresentation] :
    IsFinitelyPresentable.{u + 1} G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
