/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup

/-!
# Flattening modules by admissible blowups of algebraic spaces

A finite-type quasi-coherent module, finitely presented and flat over a
quasi-compact open of the base, has a finitely presented and flat strict
transform after an admissible blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `X` be a quasi-compact algebraic space locally of finite presentation over
a quasi-compact, absolutely quasi-separated algebraic space `B`. A finite-type
quasi-coherent module on `X` that is finitely presented and flat over a
quasi-compact open subspace `U` of `B` has a finitely presented strict transform
flat over the new base after a blowup in a finitely presented closed center
disjoint from `U`. -/
theorem exists_isAdmissibleBlowup_flattening
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B] [IsQuasiCompact X]
    (f : X ⟶ B) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [((Modules.pullback (pullback.fst f U.ι)).obj F).IsFinitePresentation]
    (h_flat : Modules.flatOver
      ((Modules.pullback (pullback.fst f U.ι)).obj F) (pullback.snd f U.ι)) :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        let F' := strictTransformModule b (Z.inverseImageSubspace b) f F
        F'.IsFinitePresentation ∧ Modules.flatOver F' (pullback.snd f b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
