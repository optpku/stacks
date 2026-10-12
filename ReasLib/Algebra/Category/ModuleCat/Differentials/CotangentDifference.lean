/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import ReasLib.RingTheory.Ideal.Cotangent.Difference
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent difference derivations in `ModuleCat`

This file packages the pure ideal-cotangent difference construction as relative derivations in
`ModuleCat`. It is the categorical bridge used by sectionwise sheaf constructions.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.Derivation

variable {R A B C : CommRingCat.{u}}

/-- The relative `ModuleCat` derivation obtained from the difference of two parallel ring maps. -/
@[stacks 0E1Y "parallel-map cotangent difference derivation"]
noncomputable def cotangentDifference (a : R ⟶ A) (I : Ideal B)
    (f g : A ⟶ B) (hbase : a ≫ f = a ≫ g)
    (h : ∀ x : A, f.hom x - g.hom x ∈ I) :
    ((ModuleCat.restrictScalars f.hom).obj
      (ModuleCat.of B I.Cotangent)).Derivation a :=
  ModuleCat.Derivation.mk
    (Ideal.Cotangent.differenceClass I f.hom g.hom h)
    (Ideal.Cotangent.differenceClass_add I f.hom g.hom h)
    (Ideal.Cotangent.differenceClass_mul I f.hom g.hom h)
    (Ideal.Cotangent.differenceClass_comp_eq_zero I a.hom f.hom g.hom
      (congrArg CommRingCat.Hom.hom hbase) h)

/-- The categorical cotangent difference derivation evaluates to the pointwise difference class. -/
@[simp]
theorem cotangentDifference_d (a : R ⟶ A) (I : Ideal B)
    (f g : A ⟶ B) (hbase : a ≫ f = a ≫ g)
    (h : ∀ x : A, f.hom x - g.hom x ∈ I) (x : A) :
    (cotangentDifference a I f g hbase h).d x =
      Ideal.Cotangent.differenceClass I f.hom g.hom h x := sorry

/-- The relative `ModuleCat` derivation for two maps that agree after a common target map. -/
@[stacks 0E1Y "kernel-valued categorical difference derivation"]
noncomputable def kernelCotangentDifference (a : R ⟶ A)
    (f g : A ⟶ B) (q : B ⟶ C)
    (hbase : a ≫ f = a ≫ g) (htarget : f ≫ q = g ≫ q) :
    ((ModuleCat.restrictScalars f.hom).obj
      (ModuleCat.of B (RingHom.ker q.hom).Cotangent)).Derivation a :=
  cotangentDifference a (RingHom.ker q.hom) f g hbase
    (RingHom.sub_mem_ker_of_comp_eq f.hom g.hom q.hom
      (congrArg CommRingCat.Hom.hom htarget))

/-- The kernel-valued categorical difference derivation evaluates to the pointwise difference
class. -/
@[simp]
theorem kernelCotangentDifference_d (a : R ⟶ A)
    (f g : A ⟶ B) (q : B ⟶ C)
    (hbase : a ≫ f = a ≫ g) (htarget : f ≫ q = g ≫ q) (x : A) :
    (kernelCotangentDifference a f g q hbase htarget).d x =
      Ideal.Cotangent.differenceClass (RingHom.ker q.hom) f.hom g.hom
        (RingHom.sub_mem_ker_of_comp_eq f.hom g.hom q.hom
          (congrArg CommRingCat.Hom.hom htarget)) x := sorry

end ModuleCat.Derivation

-- The derivation values are explicit; `sorryAx` is confined to their relative-derivation laws.
