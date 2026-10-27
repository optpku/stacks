/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Concentration

/-!
# Proper support of concentrated degree-zero cohomology

After shrinking an open neighborhood of the special fiber on which the coherator
homotopy limit is concentrated in degree zero, the finitely presented sheaf
`H^0(K)|_W` has proper support over the inverse-limit affine base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- After shrinking an open neighborhood of the special fiber on which the
coherator homotopy limit is concentrated in degree zero with finitely presented
degree-zero cohomology, that restricted cohomology has proper support over the
inverse-limit affine base. -/
theorem existsOpen_coheratorLimit_hasProperSupport
    (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (W : OpenSubspace S.space)
    (hW : IsConcentratedFinitePresentationOpen S F stageIso Klim P W) :
    ∃ W' : OpenSubspace S.space,
      W'.pointsSet ⊆ W.pointsSet ∧
        IsConcentratedFinitePresentationOpen S F stageIso Klim P W' ∧
          HasProperSupportOver (W'.ι ≫ SchemeRealization.toBase S.space)
            (restrictDegreeZero S F Klim W') :=
  sorry

/-- For a proper flat formal system and a compatibly identified tower of pushed
stage sheaves, some open neighborhood of the special fiber concentrates the
coherator homotopy limit in degree zero with finitely presented degree-zero
cohomology identified with each stage sheaf, and that restricted cohomology has
proper support over the inverse-limit affine base. -/
theorem existsOpen_coheratorLimit_concentrated_hasProperSupport
    (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (P : HomotopyLimit.Presentation
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim) :
    ∃ W : OpenSubspace S.space,
      IsConcentratedFinitePresentationOpen S F stageIso Klim P W ∧
        HasProperSupportOver (W.ι ≫ SchemeRealization.toBase S.space)
          (restrictDegreeZero S F Klim W) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
