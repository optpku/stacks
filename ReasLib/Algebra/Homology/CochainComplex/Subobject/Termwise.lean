/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Termwise Subcomplexes

A `TermwiseSubcomplex M` records chosen subobjects of every term of a homological complex and
differentials compatible with the ambient differential. It provides explicit complex and
inclusion data, together with a conversion to the canonical subobject of `M`.
-/

open CategoryTheory CategoryTheory.Limits

universe v u t

namespace HomologicalComplex

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {I : Type t} {c : ComplexShape I} (M : HomologicalComplex C c)

/-- A homological subcomplex presented by chosen subobjects in every degree and compatible
restricted differentials. -/
@[stacks 079K "termwise subcomplex"]
structure TermwiseSubcomplex where
  /-- The chosen subobject in each degree. -/
  X : ∀ i, Subobject (M.X i)
  /-- The restricted differential between chosen representatives. -/
  d : ∀ i j, (X i : C) ⟶ (X j : C)
  /-- The restricted differentials commute with the inclusions into the ambient complex. -/
  comm : ∀ i j, (X i).arrow ≫ M.d i j = d i j ≫ (X j).arrow

namespace TermwiseSubcomplex

variable {M : HomologicalComplex C c} (S : TermwiseSubcomplex M)

/-- A restricted differential vanishes outside the ambient complex shape. -/
theorem shape (i j : I) (hij : ¬c.Rel i j) : S.d i j = 0 := by
  apply (cancel_mono (S.X j).arrow).mp
  rw [← S.comm, M.shape i j hij, comp_zero, zero_comp]

/-- Consecutive restricted differentials compose to zero. -/
theorem d_comp_d (i j k : I) : S.d i j ≫ S.d j k = 0 := by
  apply (cancel_mono (S.X k).arrow).mp
  rw [Category.assoc, ← S.comm, ← Category.assoc, ← S.comm,
    Category.assoc, M.d_comp_d, comp_zero, zero_comp]

end TermwiseSubcomplex

/-- The homological complex carried by a termwise subcomplex presentation. -/
noncomputable def TermwiseSubcomplex.complex {M : HomologicalComplex C c}
    (S : TermwiseSubcomplex M) : HomologicalComplex C c where
  X := fun i ↦ S.X i
  d := S.d
  shape := fun i j hij ↦ S.shape i j hij
  d_comp_d' := fun i j k _ _ ↦ S.d_comp_d i j k

namespace TermwiseSubcomplex

variable {M : HomologicalComplex C c} (S : TermwiseSubcomplex M)

/-- The terms of the carried complex are the chosen subobjects. -/
theorem complex_X (i : I) : S.complex.X i = S.X i := rfl

/-- The differentials of the carried complex are the restricted differentials. -/
theorem complex_d (i j : I) : S.complex.d i j = S.d i j := rfl

/-- The componentwise inclusions form a morphism into the ambient complex. -/
noncomputable def inclusion : S.complex ⟶ M where
  f := fun i ↦ (S.X i).arrow
  comm' := fun i j _ ↦ S.comm i j

/-- The component of the inclusion is the chosen subobject arrow. -/
theorem inclusion_f (i : I) : S.inclusion.f i = (S.X i).arrow := rfl

/-- A termwise subcomplex inclusion is a monomorphism. -/
theorem mono_inclusion : Mono S.inclusion :=
  HomologicalComplex.mono_of_mono_f _ (fun i ↦ inferInstanceAs (Mono (S.X i).arrow))

/-- The canonical subobject of the ambient complex represented by a termwise subcomplex. -/
noncomputable def toSubobject : Subobject M :=
  @Subobject.mk _ _ _ _ S.inclusion S.mono_inclusion

/-- The chosen carried complex is canonically isomorphic to the representative selected by
`toSubobject`. -/
noncomputable def underlyingIso : (S.toSubobject : HomologicalComplex C c) ≅ S.complex :=
  @Subobject.underlyingIso _ _ _ _ S.inclusion S.mono_inclusion

end TermwiseSubcomplex
end General

namespace TermwiseSubcomplex
section Cochain

variable {C : Type u} [Category.{v} C] [Abelian C] {M : CochainComplex C ℤ}

/-- Exactness of a termwise cochain subcomplex is the expected image-kernel equality in each
degree. -/
theorem exactAt_iff_image_eq_kernel (T : TermwiseSubcomplex M) (j : ℤ) :
    T.complex.ExactAt j ↔
      imageSubobject (T.d (j - 1) j) = kernelSubobject (T.d j (j + 1)) := by
  exact (T.complex.exactAt_iff' (j := j) (i := j - 1) (k := j + 1) (by simp) (by simp)).trans
    (ShortComplex.exact_iff_image_eq_kernel _)

/-- A termwise cochain subcomplex is acyclic exactly when its restricted differentials satisfy
the degreewise image-kernel equalities. -/
theorem acyclic_iff_image_eq_kernel (T : TermwiseSubcomplex M) :
    T.complex.Acyclic ↔
      ∀ j : ℤ, imageSubobject (T.d (j - 1) j) = kernelSubobject (T.d j (j + 1)) := by
  exact forall_congr' (T.exactAt_iff_image_eq_kernel)

end Cochain

end TermwiseSubcomplex
end HomologicalComplex
