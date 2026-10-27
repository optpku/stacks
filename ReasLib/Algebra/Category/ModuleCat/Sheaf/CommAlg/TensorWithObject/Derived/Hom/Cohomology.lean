/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.RHom.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.RHom.Cohomology.CommAlg

/-!
# Cohomology of the algebra-sheaf derived tensor-Hom comparison

This leaf applies degreewise cohomology to the coefficient-generic tensor-Hom transformation.
The source and target representability equivalences come from independent derived-Hom owners;
the new API records their natural comparison and its shifted-Hom interpretation.
-/

@[expose] public section

noncomputable section

universe r u v w z g

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.Cohomology

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Degree-`n` cohomology of the source derived-Hom bifunctor. -/
@[stacks 0CS6 "source cohomology of the arbitrary-ring tensor-Hom comparison"]
noncomputable abbrev sourceFunctor
    (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    Hom.Domain K ⥤ ModuleCat.{max u z} R :=
  (Source.functor K : Hom.Domain K ⥤ DerivedCategory (ModuleCat.{max u z} R)) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u z} R) n

section WithTargetRHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

/-- Degree-`n` cohomology of derived `RHom` after tensoring both variables. -/
@[stacks 0CS6 "target cohomology of the arbitrary-ring tensor-Hom comparison"]
noncomputable abbrev targetFunctor
    (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    Hom.Domain K ⥤ ModuleCat.{max u z} R :=
  (Target.functor K : Hom.Domain K ⥤ DerivedCategory (ModuleCat.{max u z} R)) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u z} R) n

/-- The cohomology natural transformation induced by the derived tensor-Hom comparison. -/
@[stacks 0CS6 "cohomology transformation of the arbitrary-ring tensor-Hom comparison"]
noncomputable def comparison (K : Complex.{r, u, v, w, max u z} O) (n : ℤ) :
    sourceFunctor K n ⟶ targetFunctor K n :=
  Functor.whiskerRight (Hom.comparison K)
    (DerivedCategory.homologyFunctor (ModuleCat.{max u z} R) n)

/-- The degree-`n` cohomology map at a pair of derived DG modules. -/
@[stacks 0CS6 "pointwise cohomology map of the arbitrary-ring comparison"]
noncomputable abbrev cohomologyMap (K : Complex.{r, u, v, w, max u z} O)
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  (comparison K n).app (Opposite.op M, N)

end WithTargetRHom

/-- The source cohomology-to-shifted-Hom linear equivalence. -/
@[stacks 0CS6 "source representability for the arbitrary-ring comparison"]
noncomputable abbrev sourceLinearEquiv
    (K : Complex.{r, u, v, w, max u z} O)
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  DifferentialGradedModule.Derived.RHom.Cohomology.linearEquiv
    (endDGA K) M N n

section WithTargetRHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has.{r, u, v, w, max u z} O]

section TargetCohomology

variable [IsGrothendieckAbelian.{g}
  (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)]

/-- The target cohomology-to-shifted-Hom linear equivalence after derived tensoring. -/
@[stacks 0CS6 "target representability for the arbitrary-ring comparison"]
noncomputable abbrev targetLinearEquiv
    (K : Complex.{r, u, v, w, max u z} O)
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  SheafOfModules.CommAlg.Derived.RHom.Cohomology.linearEquiv
    (R := R) (J := J) (O := O)
    ((SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K).obj M)
    ((SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K).obj N) n

end TargetCohomology

set_option maxHeartbeats 800000 in
/-- Naturality of the degree-`n` cohomology comparison in both derived variables. -/
@[reassoc, stacks 0CS6 "naturality of the arbitrary-ring cohomology comparison"]
theorem comparison_naturality (K : Complex.{r, u, v, w, max u z} O) (n : ℤ)
    {X Y : Hom.Domain K} (f : X ⟶ Y) :
    (sourceFunctor K n).map f ≫ (comparison K n).app Y =
      (comparison K n).app X ≫ (targetFunctor K n).map f := sorry

section TargetCohomology

variable [IsGrothendieckAbelian.{g}
  (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)]

/-- The degree-`n` comparison is the shifted image of the source cohomology class. -/
@[stacks 0CS6 "arbitrary-ring cohomology comparison as shifted Hom map"]
theorem cohomologyMap_shiftedHom (K : Complex.{r, u, v, w, max u z} O)
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ)
    (x : (sourceFunctor K n).obj (Opposite.op M, N)) :
    targetLinearEquiv K M N n (cohomologyMap K M N n x) =
      ShiftedHom.map (sourceLinearEquiv K M N n x)
        (SheafOfModules.CommAlg.TensorWithObject.Derived.tensorFunctor K) := sorry

end TargetCohomology

end WithTargetRHom

end SheafOfModules.CommAlg.TensorWithObject.Derived.Hom.Cohomology
