/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Proper
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.TwistCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {Y P : Scheme.{u}}

/-- The derived quasicoherent pushforward associated to a represented finite locally free
projective bundle. -/
noncomputable def derivedPushforward (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] :
    DerivedQCoh P ⥤ DerivedQCoh Y := by
  -- Local instance justification (defeq pin): pin the canonical properness proof for the projective-bundle pushforward definition.
  letI : IsProper π := hπ.isProperOfFiniteLocallyFree n
  exact DerivedQCoh.pushforwardCohomologyIn π

/-- The pullback of the determinant of `ℰ`, tensored with the `-(n + 1)` twist on its
projective bundle. -/
noncomputable def relativeDualizingModule (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ) : P.Modules :=
  (Scheme.Modules.pullback π).obj (Λ[n + 1] ℰ) ⊗ hπ.twist (-((n : ℤ) + 1))

/-- The relative dualizing module of a rank-`n + 1` projective bundle is quasicoherent. -/
theorem relativeDualizingModule_isQuasicoherent (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] :
    SheafOfModules.IsQuasicoherent (relativeDualizingModule π ℰ hπ n) := sorry

/-- The shifted degree-zero relative dualizing module has quasicoherent cohomology. -/
theorem relativeDualizingObject_mem (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] :
    Scheme.ModuleDerived.quasicoherentProperty P
      (((DerivedCategory.singleFunctor P.Modules 0).obj
        (relativeDualizingModule π ℰ hπ n))⟦(n : ℤ)⟧) := sorry

/-- The relative dualizing candidate `π⁎(Λ[n + 1] ℰ) ⊗ 𝒪(-n-1)[n]` in
`DerivedQCoh P`. -/
noncomputable def relativeDualizingObject (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] : DerivedQCoh P :=
  ⟨((DerivedCategory.singleFunctor P.Modules 0).obj
      (relativeDualizingModule π ℰ hπ n))⟦(n : ℤ)⟧,
    relativeDualizingObject_mem π ℰ hπ n⟩

/-- The underlying derived module of `relativeDualizingObject` is its explicit degree-zero
module shifted by `n`. -/
theorem relativeDualizingObject_obj (π : P ⟶ Y) (ℰ : Y.Modules)
    (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ] :
    (relativeDualizingObject π ℰ hπ n).obj =
      ((DerivedCategory.singleFunctor P.Modules 0).obj
        (relativeDualizingModule π ℰ hπ n))⟦(n : ℤ)⟧ := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle

namespace AlgebraicGeometry.ProjectiveSpaceOver

variable {Y : Scheme.{u}} {n : ℕ}

/-- The derived quasicoherent pushforward associated to a chosen relative projective space. -/
noncomputable def derivedPushforward (P : ProjectiveSpaceOver Y n) :
    Scheme.DerivedQCoh P.scheme ⥤ Scheme.DerivedQCoh Y :=
  Scheme.ProjectiveBundle.derivedPushforward P.hom
    (standardModule Y n) P.isProjectiveBundle n

/-- The twist `𝒪(-n-1)`, placed in degree zero and shifted by `n`, has quasicoherent
cohomology on relative projective `n`-space. -/
theorem relativeDualizingObject_mem (P : ProjectiveSpaceOver Y n) :
    Scheme.ModuleDerived.quasicoherentProperty P.scheme
      (((DerivedCategory.singleFunctor P.scheme.Modules 0).obj
        (P.isProjectiveBundle.twist (-((n : ℤ) + 1))))⟦(n : ℤ)⟧) := sorry

/-- The relative dualizing candidate `𝒪(-n-1)[n]` on relative projective `n`-space. -/
noncomputable def relativeDualizingObject (P : ProjectiveSpaceOver Y n) :
    Scheme.DerivedQCoh P.scheme :=
  ⟨((DerivedCategory.singleFunctor P.scheme.Modules 0).obj
      (P.isProjectiveBundle.twist (-((n : ℤ) + 1))))⟦(n : ℤ)⟧,
    relativeDualizingObject_mem P⟩

/-- The underlying derived module of the relative-projective-space dualizing object is
`𝒪(-n-1)` in degree zero, shifted by `n`. -/
theorem relativeDualizingObject_obj (P : ProjectiveSpaceOver Y n) :
    (relativeDualizingObject P).obj =
      ((DerivedCategory.singleFunctor P.scheme.Modules 0).obj
        (P.isProjectiveBundle.twist (-((n : ℤ) + 1))))⟦(n : ℤ)⟧ := sorry

/-- For the standard free rank-`n + 1` module, the projective-bundle relative dualizing
object is isomorphic to `𝒪(-n-1)[n]`. -/
theorem projectiveBundleRelativeDualizing_isomorphic (P : ProjectiveSpaceOver Y n) :
    IsIsomorphic
      (Scheme.ProjectiveBundle.relativeDualizingObject P.hom
        (standardModule Y n) P.isProjectiveBundle n)
      (relativeDualizingObject P) := sorry

end AlgebraicGeometry.ProjectiveSpaceOver

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

/-- A right adjoint to the projective-bundle derived pushforward sends the structure sheaf to
the relative dualizing object. -/
theorem rightAdjointStructureSheaf_isomorphic
    {Y P : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (π : P ⟶ Y) (ℰ : Y.Modules) (hπ : Representation π ℰ) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
    (a : DerivedQCoh Y ⥤ DerivedQCoh P)
    (aAdjunction : derivedPushforward π ℰ hπ n ⊣ a) :
    IsIsomorphic (relativeDualizingObject π ℰ hπ n)
      (a.obj (DerivedQCoh.structureSheaf Y)) := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle

namespace AlgebraicGeometry.ProjectiveSpaceOver

/-- A right adjoint to relative projective-space pushforward sends the structure sheaf to the
shifted negative twist. -/
theorem rightAdjointStructureSheaf_isomorphic_twist
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] (n : ℕ)
    (P : ProjectiveSpaceOver Y n)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh P.scheme)
    (aAdjunction : derivedPushforward P ⊣ a) :
    IsIsomorphic (relativeDualizingObject P)
      (a.obj (Scheme.DerivedQCoh.structureSheaf Y)) := sorry

end AlgebraicGeometry.ProjectiveSpaceOver
