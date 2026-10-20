/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Grothendieck
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Ring.NegOnePow

/-! # Derived sheaf Hom on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree `n` product of local morphisms from degree `i` to degree `i + n`. -/
def gradedObj (F I : CochainComplex (Modules X) ℤ) (n : ℤ) : Modules X :=
  ∏ᶜ fun i : ℤ => Modules.InternalHom.obj (F.X i) (I.X (i + n))

/-- The graded commutator of the target and source differentials on sheaf Hom. -/
def differential (F I : CochainComplex (Modules X) ℤ) (n : ℤ) :
    gradedObj F I n ⟶ gradedObj F I (n + 1) :=
  Pi.lift fun i =>
    Pi.π (fun j : ℤ => Modules.InternalHom.obj (F.X j) (I.X (j + n))) i ≫
      Modules.InternalHom.post (F.X i) (I.d (i + n) (i + (n + 1))) +
    (n + 1).negOnePow •
      (Pi.π (fun j : ℤ => Modules.InternalHom.obj (F.X j) (I.X (j + n))) (i + 1) ≫
        Modules.InternalHom.pre (F.d i (i + 1)) (I.X ((i + 1) + n)) ≫
          eqToHom (congrArg (fun j => Modules.InternalHom.obj (F.X i) (I.X j))
            (show (i + 1) + n = i + (n + 1) by omega)))

/-- Two consecutive graded-commutator differentials compose to zero. -/
theorem differential_sq (F I : CochainComplex (Modules X) ℤ) (n : ℤ) :
    differential F I n ≫ differential F I (n + 1) = 0 := sorry

/-- The product-valued sheaf Hom complex with its graded-commutator differential. -/
def complex (F I : CochainComplex (Modules X) ℤ) : CochainComplex (Modules X) ℤ :=
  CochainComplex.of (gradedObj F I) (differential F I) (differential_sq F I)

/-- Derived sheaf Hom computed from a source representative and a K-injective replacement. -/
def obj (E N : ModuleDerived X) : ModuleDerived X :=
  DerivedCategory.Q.obj (complex
    (DerivedCategory.Q.objPreimage E)
    ((CochainComplex.KInjectiveResolution.Construction.replacement.{u} (Modules X)).obj
      (DerivedCategory.Q.objPreimage N)))

/-- Any source representative and K-injective target representative compute derived sheaf Hom. -/
theorem obj_model (E N : ModuleDerived X) (F I : CochainComplex (Modules X) ℤ)
    [I.IsKInjective] (sourceIso : DerivedCategory.Q.obj F ≅ E)
    (targetIso : DerivedCategory.Q.obj I ≅ N) :
    IsIsomorphic (obj E N) (DerivedCategory.Q.obj (complex F I)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
