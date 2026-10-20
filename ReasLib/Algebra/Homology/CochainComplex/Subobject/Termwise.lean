module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
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
theorem shape (i j : I) (hij : ¬c.Rel i j) : S.d i j = 0 := sorry

/-- Consecutive restricted differentials compose to zero. -/
theorem d_comp_d (i j k : I) : S.d i j ≫ S.d j k = 0 := sorry

/-- The homological complex carried by a termwise subcomplex presentation. -/
noncomputable def complex : HomologicalComplex C c where
  X := fun i ↦ S.X i
  d := S.d
  shape := fun i j hij ↦ S.shape i j hij
  d_comp_d' := fun i j k _ _ ↦ S.d_comp_d i j k

/-- The terms of the carried complex are the chosen subobjects. -/
theorem complex_X (i : I) : S.complex.X i = S.X i := sorry

/-- The differentials of the carried complex are the restricted differentials. -/
theorem complex_d (i j : I) : S.complex.d i j = S.d i j := sorry

/-- The componentwise inclusions form a morphism into the ambient complex. -/
noncomputable def inclusion : S.complex ⟶ M where
  f := fun i ↦ (S.X i).arrow
  comm' := fun i j _ ↦ S.comm i j

/-- The component of the inclusion is the chosen subobject arrow. -/
theorem inclusion_f (i : I) : S.inclusion.f i = (S.X i).arrow := sorry

/-- A termwise subcomplex inclusion is a monomorphism. -/
@[instance] theorem mono_inclusion : Mono S.inclusion := sorry

/-- The canonical subobject of the ambient complex represented by a termwise subcomplex. -/
noncomputable def toSubobject : Subobject M :=
  Subobject.mk S.inclusion

/-- The chosen carried complex is canonically isomorphic to the representative selected by
`toSubobject`. -/
noncomputable def underlyingIso : (S.toSubobject : HomologicalComplex C c) ≅ S.complex :=
  Subobject.underlyingIso S.inclusion

section Cochain

variable [Abelian C] {M : CochainComplex C ℤ}

/-- Exactness of a termwise cochain subcomplex is the expected image-kernel equality in each
degree. -/
theorem exactAt_iff_image_eq_kernel (T : TermwiseSubcomplex M) (j : ℤ) :
    T.complex.ExactAt j ↔
      imageSubobject (T.d (j - 1) j) = kernelSubobject (T.d j (j + 1)) := sorry

/-- A termwise cochain subcomplex is acyclic exactly when its restricted differentials satisfy
the degreewise image-kernel equalities. -/
theorem acyclic_iff_image_eq_kernel (T : TermwiseSubcomplex M) :
    T.complex.Acyclic ↔
      ∀ j : ℤ, imageSubobject (T.d (j - 1) j) = kernelSubobject (T.d j (j + 1)) := sorry

end Cochain

end TermwiseSubcomplex
end HomologicalComplex
