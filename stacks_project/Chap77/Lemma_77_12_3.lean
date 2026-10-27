/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

universe u

/- Lemma 77.12.3: The tensor global-sections complex is perfect over the limit ring. -/
@[stacks 0CX6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.globalSectionsTensor_isPerfect :
  ∀ (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E),
    DerivedCategory.IsPerfect (globalSectionsTensor S F Klim E))

/- Lemma 77.12.3: The canonical tensor base-change map at every finite stage is invertible. -/
@[stacks 0CX6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.globalSectionsTensorBaseChangeMap_isIso :
  ∀ (S : ProperFlatFormalSystem)
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
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom),
    IsIso (globalSectionsTensorBaseChangeMap S F stageIso Klim P E n Ext))

/- Lemma 77.12.3: The derived global Hom complex is perfect over the limit ring. -/
@[stacks 0CX6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.globalHom_isPerfect :
  ∀ (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (stageIso_naturality : ∀ n,
      (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ pushforwardStep S n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E),
    DerivedCategory.IsPerfect (globalHom S F Klim E))

/- Lemma 77.12.3: The canonical derived Hom base-change map at every finite stage is invertible. -/
@[stacks 0CX6] #check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.globalHomBaseChangeMap_isIso :
  ∀ (S : ProperFlatFormalSystem)
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
        DerivedCategory.singleFunctor (Modules S.space) (0 : ℤ)) Klim)
    (n : ℕ)
    (E : ModuleDerived S.space) (hE : ModuleDerived.IsPerfect E)
    (Ext : ModuleCat.DerivedExtension (S.limitCone.cone.stageMap n).hom),
    IsIso (globalHomBaseChangeMap S F stageIso Klim P n E Ext))

