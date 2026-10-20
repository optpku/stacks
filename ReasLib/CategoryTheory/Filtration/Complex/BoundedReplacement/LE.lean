/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Strict.FiniteKernelCokernel
public import ReasLib.CategoryTheory.Filtration.KernelCokernel.Universal
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Upper Truncation of Filtered Complexes

This file constructs the filtered analogue of good upper truncation.  At the cutoff it uses the
canonical filtered kernel, so the object, differential, inclusion, and lift are genuine data.
Finiteness, support, and associated-graded quasi-isomorphism are exposed separately.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

open FilteredObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace TruncLE

/-- The degree-`n` filtered object in the good upper truncation at `b`. -/
@[stacks 05S5 "filtered upper truncation"]
noncomputable def obj (K : FilteredComplex A) (b n : ℤ) : FilteredObject A :=
  if _ : n < b then K.X n
  else if _ : n = b then Hom.kernel (K.d b (b + 1))
  else 0

/-- Below the cutoff, the good upper truncation retains the original filtered object. -/
@[stacks 05S5 "filtered upper truncation", simp]
theorem obj_eq_self (K : FilteredComplex A) (b n : ℤ) (hn : n < b) :
    obj K b n = K.X n := sorry

/-- At the cutoff, the good upper truncation is the filtered kernel of the outgoing
differential. -/
@[stacks 05S5 "filtered upper truncation", simp]
theorem obj_eq_kernel (K : FilteredComplex A) (b n : ℤ) (hn : n = b) :
    obj K b n = Hom.kernel (K.d b (b + 1)) := sorry

/-- Above the cutoff, the good upper truncation is zero. -/
@[stacks 05S5 "filtered upper truncation", simp]
theorem obj_eq_zero (K : FilteredComplex A) (b n : ℤ) (hn : b < n) :
    obj K b n = 0 := sorry

/-- A cochain differential ending at the cutoff starts strictly below it. -/
theorem source_lt (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hj : j = b) :
    i < b := sorry

/-- A cochain differential ending below the cutoff also starts below it. -/
theorem source_lt_of_lt (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hj : j < b) :
    i < b := sorry

/-- Every incoming differential to the cutoff composes trivially with its outgoing
differential. -/
theorem cutoff_comp (K : FilteredComplex A) (i b : ℤ) :
    K.d i b ≫ K.d b (b + 1) = 0 := sorry

/-- The differential on the good upper truncation. -/
@[stacks 05S5 "filtered upper truncation"]
noncomputable def d (K : FilteredComplex A) (b i j : ℤ) : obj K b i ⟶ obj K b j :=
  if hij : (ComplexShape.up ℤ).Rel i j then
    if hj : j = b then
      eqToHom (obj_eq_self K b i (source_lt b i j hij hj)) ≫
        Hom.kernelLift (K.d b (b + 1)) (K.d i b) (cutoff_comp K i b) ≫
        eqToHom (obj_eq_kernel K b j hj).symm
    else if hjb : j < b then
      eqToHom (obj_eq_self K b i (source_lt_of_lt b i j hij hjb)) ≫ K.d i j ≫
        eqToHom (obj_eq_self K b j hjb).symm
    else 0
  else 0

/-- The upper-truncation differential vanishes away from the cochain shape. -/
theorem shape (K : FilteredComplex A) (b i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel i j) : d K b i j = 0 := sorry

/-- Consecutive upper-truncation differentials compose to zero. -/
theorem d_comp_d (K : FilteredComplex A) (b i j k : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    d K b i j ≫ d K b j k = 0 := sorry

end TruncLE

/-- The good upper truncation of a filtered cochain complex. -/
@[stacks 05S5 "filtered upper truncation"]
noncomputable def truncLE (K : FilteredComplex A) (b : ℤ) : FilteredComplex A where
  X := TruncLE.obj K b
  d := TruncLE.d K b
  shape := TruncLE.shape K b
  d_comp_d' := TruncLE.d_comp_d K b

namespace TruncLE

/-- Evaluation of good upper truncation on an object degree. -/
@[stacks 05S5 "filtered upper truncation", simp]
theorem complex_X (K : FilteredComplex A) (b n : ℤ) :
    (truncLE K b).X n = obj K b n := sorry

/-- Evaluation of the good upper-truncation differential. -/
@[stacks 05S5 "filtered upper truncation", simp]
theorem complex_d (K : FilteredComplex A) (b i j : ℤ) :
    (truncLE K b).d i j = d K b i j := sorry

/-- The degreewise component of the canonical inclusion from good upper truncation. -/
@[stacks 05S5 "filtered upper truncation inclusion"]
noncomputable def ιComponent (K : FilteredComplex A) (b n : ℤ) : obj K b n ⟶ K.X n :=
  if hnb : n < b then eqToHom (obj_eq_self K b n hnb)
  else if hbn : n = b then
    eqToHom (obj_eq_kernel K b n hbn) ≫ Hom.kernelι (K.d b (b + 1)) ≫
      eqToHom (congrArg (fun m : ℤ ↦ K.X m) hbn).symm
  else if _ : b < n then 0
  else 0

/-- The upper-truncation inclusion commutes with differentials. -/
theorem ι_comm (K : FilteredComplex A) (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ιComponent K b i ≫ K.d i j = d K b i j ≫ ιComponent K b j := sorry

end TruncLE

/-- The canonical inclusion from good upper truncation into a filtered complex. -/
@[stacks 05S5 "filtered upper truncation inclusion"]
noncomputable def ιTruncLE (K : FilteredComplex A) (b : ℤ) : truncLE K b ⟶ K where
  f := TruncLE.ιComponent K b
  comm' := TruncLE.ι_comm K b

namespace TruncLE

/-- Evaluation of the canonical upper-truncation inclusion in one degree. -/
@[stacks 05S5 "filtered upper truncation inclusion", simp]
theorem ι_f (K : FilteredComplex A) (b n : ℤ) :
    (ιTruncLE K b).f n = ιComponent K b n := sorry

/-- Good upper truncation preserves termwise finite filtrations. -/
@[stacks 05S5 "filtered upper truncation"]
theorem finite (K : FilteredComplex A) (hK : K.HasFiniteFiltrations) (b : ℤ) :
    (truncLE K b).HasFiniteFiltrations := sorry

/-- Good upper truncation is strictly bounded above after forgetting the filtration. -/
@[stacks 05S5 "filtered upper truncation"]
theorem isStrictlyLE (K : FilteredComplex A) (b : ℤ) :
    (truncLE K b).underlying.IsStrictlyLE b := sorry

/-- Good upper truncation preserves a strict lower bound. -/
@[stacks 05S5 "filtered upper truncation"]
theorem isStrictlyGE (K : FilteredComplex A) (a b : ℤ)
    (hK : K.underlying.IsStrictlyGE a) :
    (truncLE K b).underlying.IsStrictlyGE a := sorry

/-- Under upper cohomological boundedness of the associated graded complex, the canonical upper
truncation inclusion is a filtered quasi-isomorphism. -/
@[stacks 05S5 "filtered upper truncation quasi-isomorphism"]
theorem quasiIso_ι (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hK : K.associatedGraded.IsLE b) :
    QuasiIso (associatedGradedMap (ιTruncLE K b)) := sorry

/-- The outgoing differential kills the cutoff component of any map from a complex strictly
bounded above at the cutoff. -/
theorem comp_outgoing {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) :
    f.f b ≫ K.d b (b + 1) = 0 := sorry

/-- The degreewise component of a lift through good upper truncation. -/
@[stacks 05S5 "filtered upper truncation lift"]
noncomputable def liftComponent {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) (n : ℤ) : L.X n ⟶ obj K b n :=
  if hnb : n < b then f.f n ≫ eqToHom (obj_eq_self K b n hnb).symm
  else if hbn : n = b then
    eqToHom (congrArg (fun m : ℤ ↦ L.X m) hbn) ≫
      Hom.kernelLift (K.d b (b + 1)) (f.f b) (comp_outgoing b f hL) ≫
      eqToHom (obj_eq_kernel K b n hbn).symm
  else if _ : b < n then 0
  else 0

/-- A lift through good upper truncation commutes with differentials. -/
theorem lift_comm {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    liftComponent b f hL i ≫ d K b i j = L.d i j ≫ liftComponent b f hL j := sorry

/-- Any map from a complex strictly bounded above at `b` lifts through good upper truncation. -/
@[stacks 05S5 "filtered upper truncation lift"]
noncomputable def lift {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) : L ⟶ truncLE K b where
  f := liftComponent b f hL
  comm' := lift_comm b f hL

/-- Evaluation of a lift through good upper truncation in one degree. -/
@[stacks 05S5 "filtered upper truncation lift", simp]
theorem lift_f {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) (n : ℤ) :
    (lift b f hL).f n = liftComponent b f hL n := sorry

/-- A lift followed by the upper-truncation inclusion recovers the original map. -/
@[stacks 05S5 "filtered upper truncation lift"]
theorem lift_ι {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) :
    lift b f hL ≫ ιTruncLE K b = f := sorry

/-- If `f` and the canonical upper-truncation inclusion are filtered quasi-isomorphisms, then
the lifted map is a filtered quasi-isomorphism as well. -/
@[stacks 05S5 "filtered upper truncation lift"]
theorem quasiIso_lift {L K : FilteredComplex A} (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hK : K.associatedGraded.IsLE b) (f : L ⟶ K)
    (hf : QuasiIso (associatedGradedMap f)) (hL : L.underlying.IsStrictlyLE b) :
    QuasiIso (associatedGradedMap (lift b f hL)) := sorry

end TruncLE

end CategoryTheory.FilteredComplex
