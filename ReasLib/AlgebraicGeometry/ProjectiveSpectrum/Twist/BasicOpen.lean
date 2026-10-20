/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Shift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Twisting sheaves on projective basic opens

Canonical twisting sheaves are associated sheaves of translated regular gradings. Explicit
multiplication and module-shift comparisons are specified by their homogeneous-fraction formulas
on standard opens.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u v

namespace AlgebraicGeometry

section Restriction

variable {A : Type u} {σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The module restriction functor from a projective spectrum to one of its basic opens. -/
abbrev basicOpenRestrict (f : A) :
    (Proj 𝒜).Modules ⥤ (Proj.basicOpen 𝒜 f).toScheme.Modules :=
  Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f).ι

end Restriction

namespace Proj.AssociatedModule

section TwistingSheaf

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The canonical twisting sheaf of index n is the sheaf associated to the regular grading
translated by n. -/
@[stacks 01CV "canonical twisting sheaf"]
noncomputable def twistingSheaf (n : ℤ) : (Proj 𝒜).Modules :=
  sheaf (R := R) (A := A) (M := A) 𝒜
    (GradedModule.shiftGrading (DirectSum.Decomposition.natToIntGrading 𝒜) n)

end TwistingSheaf

variable {A M : Type u} [CommRing A]
variable [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- Explicit multiplication morphisms between canonical twisting sheaves, together with their
standard-open formula as multiplication of homogeneous fractions. -/
structure TwistMultiplication where
  /-- The morphism multiplying twists of indices a and b. -/
  hom :
    ∀ a b : ℤ,
      (tensorObj (twistingSheaf (R := ℤ) (A := A) 𝒜 a)
        (twistingSheaf (R := ℤ) (A := A) 𝒜 b) : (Proj 𝒜).Modules) ⟶
        twistingSheaf (R := ℤ) (A := A) 𝒜 (a + b)
  /-- On every positive-degree standard open, applying hom to two fraction sections gives a
  fraction section represented by the product of the localized fractions. -/
  standardOpen_formula :
    ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (a b : ℤ)
      (x : away 𝒜
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) a) f)
      (y : away 𝒜
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) b) f),
      ∃ z : away 𝒜
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) (a + b)) f,
        (z : LocalizedModule.Away (f : A) A) =
            (x : LocalizedModule.Away (f : A) A) *
              (y : LocalizedModule.Away (f : A) A) ∧
          (((hom a b).val.app
              (Opposite.op (Proj.basicOpen 𝒜 (f : A)))).hom
            (SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf
              (Opposite.op (Proj.basicOpen 𝒜 (f : A)))
              (awaySection 𝒜
                (GradedModule.shiftGrading
                  (DirectSum.Decomposition.natToIntGrading 𝒜) a) f hd x)
              (awaySection 𝒜
                (GradedModule.shiftGrading
                  (DirectSum.Decomposition.natToIntGrading 𝒜) b) f hd y))) =
            awaySection 𝒜
              (GradedModule.shiftGrading
                (DirectSum.Decomposition.natToIntGrading 𝒜) (a + b)) f hd z

namespace TwistMultiplication

/-- Construct canonical-twist multiplication data from explicit morphisms satisfying the
standard-open homogeneous-fraction formula. -/
def ofHom
    (hom :
      ∀ a b : ℤ,
        (tensorObj (twistingSheaf (R := ℤ) (A := A) 𝒜 a)
          (twistingSheaf (R := ℤ) (A := A) 𝒜 b) : (Proj 𝒜).Modules) ⟶
          twistingSheaf (R := ℤ) (A := A) 𝒜 (a + b))
    (standardOpen_formula :
      ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (a b : ℤ)
        (x : away 𝒜
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) a) f)
        (y : away 𝒜
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) b) f),
        ∃ z : away 𝒜
            (GradedModule.shiftGrading
              (DirectSum.Decomposition.natToIntGrading 𝒜) (a + b)) f,
          (z : LocalizedModule.Away (f : A) A) =
              (x : LocalizedModule.Away (f : A) A) *
                (y : LocalizedModule.Away (f : A) A) ∧
            (((hom a b).val.app
                (Opposite.op (Proj.basicOpen 𝒜 (f : A)))).hom
              (SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf
                (Opposite.op (Proj.basicOpen 𝒜 (f : A)))
                (awaySection 𝒜
                  (GradedModule.shiftGrading
                    (DirectSum.Decomposition.natToIntGrading 𝒜) a) f hd x)
                (awaySection 𝒜
                  (GradedModule.shiftGrading
                    (DirectSum.Decomposition.natToIntGrading 𝒜) b) f hd y))) =
              awaySection 𝒜
                (GradedModule.shiftGrading
                  (DirectSum.Decomposition.natToIntGrading 𝒜) (a + b)) f hd z) :
    TwistMultiplication 𝒜 where
  hom := hom
  standardOpen_formula := standardOpen_formula

end TwistMultiplication

/-- Explicit comparison morphisms from an associated module sheaf tensored with a canonical
twist to the associated sheaf of the translated module grading, with their standard-open
homogeneous-fraction formula. -/
@[stacks 0B5R "associated-module shift comparison data"]
structure ShiftComparison where
  /-- The comparison from M̃ ⊗ 𝒪(k) to the associated sheaf of the grading translated by k. -/
  hom :
    ∀ k : ℤ,
      (tensorObj (sheaf 𝒜 ℳ) (twistingSheaf (R := ℤ) (A := A) 𝒜 k) :
        (Proj 𝒜).Modules) ⟶
        sheaf 𝒜 (GradedModule.shiftGrading ℳ k)
  /-- On every positive-degree standard open, the comparison sends a pure tensor of fraction
  sections to the fraction represented by the localized scalar action. -/
  standardOpen_formula :
    ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (k : ℤ)
      (x : away 𝒜 ℳ f)
      (y : away 𝒜
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) k) f),
      ∃ z : away 𝒜 (GradedModule.shiftGrading ℳ k) f,
        (z : LocalizedModule.Away (f : A) M) =
            (y : LocalizedModule.Away (f : A) A) •
              (x : LocalizedModule.Away (f : A) M) ∧
          (((hom k).val.app
              (Opposite.op (Proj.basicOpen 𝒜 (f : A)))).hom
            (SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf
              (Opposite.op (Proj.basicOpen 𝒜 (f : A)))
              (awaySection 𝒜 ℳ f hd x)
              (awaySection 𝒜
                (GradedModule.shiftGrading
                  (DirectSum.Decomposition.natToIntGrading 𝒜) k) f hd y))) =
            awaySection 𝒜 (GradedModule.shiftGrading ℳ k) f hd z

namespace ShiftComparison

/-- Construct associated-module shift-comparison data from explicit morphisms satisfying the
standard-open homogeneous-fraction formula. -/
@[stacks 0B5R "constructor for associated-module shift comparisons"]
def ofHom
    (hom :
      ∀ k : ℤ,
        (tensorObj (sheaf 𝒜 ℳ) (twistingSheaf (R := ℤ) (A := A) 𝒜 k) :
          (Proj 𝒜).Modules) ⟶
          sheaf 𝒜 (GradedModule.shiftGrading ℳ k))
    (standardOpen_formula :
      ∀ {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (k : ℤ)
        (x : away 𝒜 ℳ f)
        (y : away 𝒜
          (GradedModule.shiftGrading
            (DirectSum.Decomposition.natToIntGrading 𝒜) k) f),
        ∃ z : away 𝒜 (GradedModule.shiftGrading ℳ k) f,
          (z : LocalizedModule.Away (f : A) M) =
              (y : LocalizedModule.Away (f : A) A) •
                (x : LocalizedModule.Away (f : A) M) ∧
            (((hom k).val.app
                (Opposite.op (Proj.basicOpen 𝒜 (f : A)))).hom
              (SheafOfModules.RingedSite.tensorSection (Proj 𝒜).sheaf
                (Opposite.op (Proj.basicOpen 𝒜 (f : A)))
                (awaySection 𝒜 ℳ f hd x)
                (awaySection 𝒜
                  (GradedModule.shiftGrading
                    (DirectSum.Decomposition.natToIntGrading 𝒜) k) f hd y))) =
              awaySection 𝒜 (GradedModule.shiftGrading ℳ k) f hd z) :
    ShiftComparison 𝒜 ℳ where
  hom := hom
  standardOpen_formula := standardOpen_formula

/-- Restrict an associated-module shift comparison to a projective basic open. -/
def restrictBasicOpenMap
    (C : ShiftComparison 𝒜 ℳ) (f : A) (k : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 f).toScheme.Modules]
    [(basicOpenRestrict 𝒜 f).LaxMonoidal] :
    (tensorObj
      ((basicOpenRestrict 𝒜 f).obj (sheaf 𝒜 ℳ))
      ((basicOpenRestrict 𝒜 f).obj (twistingSheaf (R := ℤ) (A := A) 𝒜 k)) :
      (Proj.basicOpen 𝒜 f).toScheme.Modules) ⟶
      (basicOpenRestrict 𝒜 f).obj
        (sheaf 𝒜 (GradedModule.shiftGrading ℳ k)) :=
  Functor.LaxMonoidal.μ (basicOpenRestrict 𝒜 f)
      (sheaf 𝒜 ℳ) (twistingSheaf (R := ℤ) (A := A) 𝒜 k) ≫
    (basicOpenRestrict 𝒜 f).map (C.hom k)

/-- A standard-open-specified comparison with the associated sheaf of a translated grading is
an isomorphism on a positive-degree basic open at every degree divisible by its defining degree. -/
theorem restrictBasicOpen_isIso
    (C : ShiftComparison 𝒜 ℳ) {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
    [(basicOpenRestrict 𝒜 (f : A)).LaxMonoidal] :
    IsIso
      (restrictBasicOpenMap 𝒜 ℳ C (f : A) (n * (d : ℤ))) := sorry

end ShiftComparison

end Proj.AssociatedModule

namespace Proj.AssociatedModule

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

namespace Twist

/-- The restriction of every twist whose index is divisible by the degree of a positive-degree
homogeneous element is trivial on the corresponding projective basic open. -/
theorem restrictBasicOpen_isTrivial
    {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ) :
    RingedSpace.IsTrivial
      ((basicOpenRestrict 𝒜 (f : A)).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜
          (n * (d : ℤ)))) := sorry

/-- The restriction of every twist whose index is divisible by the degree of a positive-degree
homogeneous element is invertible on the corresponding projective basic open. -/
theorem restrictBasicOpen_invertible
    {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ) :
    MonoidalCategory.isInvertibleObject
      ((basicOpenRestrict 𝒜 (f : A)).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜
          (n * (d : ℤ)))) := sorry

end Twist

namespace TwistMultiplication

/-- Restrict a canonical twisting-sheaf multiplication morphism to a projective basic open. -/
def restrictBasicOpenMap
    (T : TwistMultiplication 𝒜)
    (f : A) (a b : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 f).toScheme.Modules]
    [(basicOpenRestrict 𝒜 f).LaxMonoidal] :
    (tensorObj
      ((basicOpenRestrict 𝒜 f).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 a))
      ((basicOpenRestrict 𝒜 f).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 b)) :
      (Proj.basicOpen 𝒜 f).toScheme.Modules) ⟶
      (basicOpenRestrict 𝒜 f).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 (a + b)) :=
  Functor.LaxMonoidal.μ (basicOpenRestrict 𝒜 f)
      (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 a)
      (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 b) ≫
    (basicOpenRestrict 𝒜 f).map (T.hom a b)

/-- A standard-open-specified multiplication of canonical twists is an isomorphism after
restriction when its first degree is divisible by the degree defining the basic open. -/
theorem restrictBasicOpen_isIso
    (T : TwistMultiplication 𝒜)
    {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n m : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
    [(basicOpenRestrict 𝒜 (f : A)).LaxMonoidal] :
    IsIso
      (restrictBasicOpenMap 𝒜 T (f : A)
        (n * (d : ℤ)) m) := sorry

end TwistMultiplication

namespace TwistAction

/-- Restrict the action of a canonical twist on a module tensored with another canonical twist
to a projective basic open. -/
def restrictBasicOpenMap
    (T : TwistMultiplication 𝒜)
    (f : A) (ℱ : (Proj 𝒜).Modules) (a b : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 f).toScheme.Modules]
    [(basicOpenRestrict 𝒜 f).LaxMonoidal] :
    (tensorObj
      ((basicOpenRestrict 𝒜 f).obj
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 a))
      ((basicOpenRestrict 𝒜 f).obj
        (tensorObj ℱ
          (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 b))) :
      (Proj.basicOpen 𝒜 f).toScheme.Modules) ⟶
      (basicOpenRestrict 𝒜 f).obj
        (tensorObj ℱ
          (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 (a + b))) :=
  Functor.LaxMonoidal.μ (basicOpenRestrict 𝒜 f)
      (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 a)
      (tensorObj ℱ
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜 b)) ≫
    (basicOpenRestrict 𝒜 f).map
      (projSheafTwistMul 𝒜
        (Proj.AssociatedModule.twistingSheaf (R := ℤ) (A := A) 𝒜) T.hom ℱ a b)

/-- The action of a standard-open-specified canonical twist multiplication on any module sheaf
is an isomorphism after restriction when the twist degree is divisible by the basic-open degree. -/
theorem restrictBasicOpen_isIso
    (T : TwistMultiplication 𝒜)
    (ℱ : (Proj 𝒜).Modules)
    {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n m : ℤ)
    [MonoidalCategory (Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
    [(basicOpenRestrict 𝒜 (f : A)).LaxMonoidal] :
    IsIso
      (restrictBasicOpenMap 𝒜 T (f : A) ℱ
        (n * (d : ℤ)) m) := sorry

end TwistAction

end Proj.AssociatedModule

end AlgebraicGeometry
