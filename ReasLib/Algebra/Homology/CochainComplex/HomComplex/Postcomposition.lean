/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Postcomposition on Hom Complexes

For `ℤ`-indexed cochain complexes in a preadditive category, this file owns the covariant
action of a target morphism on the Hom complex out of a fixed source.  It is the target-variable
counterpart of `homComplexPrecomp`.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.HomComplex

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Postcomposition by a cochain-complex morphism sends the zero cochain to zero. -/
theorem homComplexPostcomp_map_zero
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) :
    (0 : CochainComplex.HomComplex.Cochain N I n).comp
        (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) =
      (0 : CochainComplex.HomComplex.Cochain N J n) := sorry

/-- Postcomposition on fixed-degree Hom-complex cochains is additive. -/
theorem homComplexPostcomp_map_add
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain N I n) :
    (z + z').comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) +
        z'.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) := sorry

/-- Postcomposition with a cochain-complex morphism as an additive map on fixed-degree
cochains. -/
noncomputable def homComplexPostcompAddMonoidHom
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) :
    CochainComplex.HomComplex.Cochain N I n →+
      CochainComplex.HomComplex.Cochain N J n where
  toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)
  map_zero' := homComplexPostcomp_map_zero f n
  map_add' := homComplexPostcomp_map_add f n

/-- Evaluation of the fixed-degree postcomposition map is composition with the zero cochain
of `f`. -/
@[simp]
theorem homComplexPostcompAddMonoidHom_apply
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain N I n) :
    homComplexPostcompAddMonoidHom (N := N) f n z =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n) := sorry

/-- The component formula for fixed-degree Hom-complex postcomposition. -/
@[simp]
theorem homComplexPostcompAddMonoidHom_v
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain N I n) (p q : ℤ) (hpq : p + n = q) :
    (homComplexPostcompAddMonoidHom (N := N) f n z).v p q hpq =
      z.v p q hpq ≫ f.f q := sorry

/-- The fixed-degree postcomposition maps commute with the Hom-complex differential. -/
theorem homComplexPostcomp_comm
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (i j : ℤ)
    (h_ij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom (N := N) f i) ≫
        (CochainComplex.HomComplex N J).d i j =
      (CochainComplex.HomComplex N I).d i j ≫
        AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom (N := N) f j) := sorry

/-- Postcomposition with a cochain-complex morphism as a chain map between Hom complexes. -/
@[stacks 079L "Hom-complex postcomposition"]
noncomputable def homComplexPostcomp
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) :
    CochainComplex.HomComplex N I ⟶ CochainComplex.HomComplex N J where
  f n := AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom (N := N) f n)
  comm' := homComplexPostcomp_comm (N := N) f

/-- The degree-`n` component of `homComplexPostcomp` is fixed-degree postcomposition. -/
@[simp]
theorem homComplexPostcomp_f
    {N I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) :
    (homComplexPostcomp (N := N) f).f n =
      AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom (N := N) f n) := sorry

/-- Hom-complex postcomposition is covariantly functorial under composition of target maps. -/
theorem homComplexPostcomp_comp
    {N I J K : CochainComplex C ℤ} (f : I ⟶ J) (g : J ⟶ K) :
    homComplexPostcomp (N := N) (f ≫ g) =
      homComplexPostcomp (N := N) f ≫ homComplexPostcomp (N := N) g := sorry

/-- Postcomposition by the identity is the identity of the Hom complex. -/
@[simp]
theorem homComplexPostcomp_id
    {N I : CochainComplex C ℤ} :
    homComplexPostcomp (N := N) (𝟙 I) = 𝟙 (CochainComplex.HomComplex N I) := sorry

end CategoryTheory.CochainComplex
