/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Example_75_19_5_HomotopyLimit
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Homotopy limits of pushed stage sheaves

The stage modules of a proper flat formal system are viewed on the limit space by
pushforward along the closed immersions `X_n ⟶ X`. An ambient homotopy limit of
those pushforwards has quasi-coherent coreflection in `Dᵇ_QCoh(𝒪_X)` with vanishing
cohomology in negative degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The stage module sheaf `ℱ n`, viewed as a sheaf on `X` by pushforward along the
closed immersion `stageToSpace n : X_n ⟶ X`. -/
def pushforwardModule (S : ProperFlatFormalSystem) (n : ℕ) : S.space.Modules :=
  (Modules.pushforward (S.stageToSpace n)).obj (S.moduleSheaf n)

/-- `pushforwardModule` is the underived pushforward of the stage module sheaf along
the closed immersion to the limit space. -/
theorem pushforwardModule_spec (S : ProperFlatFormalSystem) (n : ℕ) :
    S.pushforwardModule n = (Modules.pushforward (S.stageToSpace n)).obj (S.moduleSheaf n) :=
  sorry

/-- Pushforward of a finitely presented stage module along the closed immersion
`X_n ⟶ X` is quasi-coherent on `X`. -/
instance pushforwardModule_isQuasicoherent (S : ProperFlatFormalSystem) (n : ℕ) :
    (S.pushforwardModule n).IsQuasicoherent :=
  sorry

/-- The quasi-coherent coreflection of an ambient homotopy limit of the pushed stage
sheaves is bounded above and has vanishing cohomology sheaves in negative degrees. -/
theorem coheratorHomotopyLimit_isBounded (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor S.space.Modules (0 : ℤ)) Klim) :
    ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj.IsGE 0 ∧
      DerivedCategory.IsBoundedAbove
        ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj :=
  sorry

/-- The cohomology-in property of quasi-coherent modules on the limit space is a
triangulated subcategory of `D(𝒪_X)`. -/
instance derivedQuasiCoherent_isTriangulated (S : ProperFlatFormalSystem) :
    (derivedQuasiCoherentModuleProperty S.space).IsTriangulated :=
  sorry

/-- The cohomology-in property of quasi-coherent modules on the limit space is
stable under integral shifts. -/
instance derivedQuasiCoherent_isStableUnderShift (S : ProperFlatFormalSystem) :
    (derivedQuasiCoherentModuleProperty S.space).IsStableUnderShift ℤ :=
  sorry

/-- The derived category of quasi-coherent cohomology on the limit space has a
zero object. -/
instance derivedQCoh_hasZeroObject (S : ProperFlatFormalSystem) :
    HasZeroObject (DerivedQCoh S.space) :=
  sorry

/-- The integral shift on `DerivedQCoh` of the limit space. -/
noncomputable instance derivedQCoh_hasShift (S : ProperFlatFormalSystem) :
    HasShift (DerivedQCoh S.space) ℤ :=
  ObjectProperty.hasShift (derivedQuasiCoherentModuleProperty S.space)

/-- Each integral shift functor on `DerivedQCoh` of the limit space is additive. -/
instance derivedQCoh_shiftFunctor_additive (S : ProperFlatFormalSystem) (n : ℤ) :
    (shiftFunctor (DerivedQCoh S.space) n).Additive :=
  sorry

/-- The coherator of an ambient homotopy limit of the pushed stage sheaves is a
homotopy limit in `DerivedQCoh` of the coreflected degree-zero system. -/
theorem coheratorHomotopyLimit_isHomotopyLimit (S : ProperFlatFormalSystem)
    [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
    (F : SequentialInverseSystem (QCoh S.space))
    (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
      S.pushforwardModule n)
    (Klim : ModuleDerived S.space)
    (hKlim : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor S.space.Modules (0 : ℤ)) Klim) :
    HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion S.space ⋙
        DerivedCategory.singleFunctor S.space.Modules (0 : ℤ) ⋙
        (DerivedQCoh.inclusion S.space).rightAdjoint)
      ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
