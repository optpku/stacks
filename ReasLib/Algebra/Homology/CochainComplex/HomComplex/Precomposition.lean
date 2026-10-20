module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition on Hom Complexes

For `ℤ`-indexed cochain complexes in a preadditive category, this file owns
the contravariant action of a source morphism on the Hom complex into a fixed
target.  It exposes the degreewise additive map, its chain-map assembly, and
the computation and functoriality API needed by derived and homotopy-category
arguments.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.HomComplex

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Precomposition by a cochain-complex morphism sends the zero cochain to zero. -/
theorem homComplexPrecomp_map_zero
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) :
    (CochainComplex.HomComplex.Cochain.ofHom f).comp
        (0 : CochainComplex.HomComplex.Cochain M I n) (zero_add n) =
      (0 : CochainComplex.HomComplex.Cochain L I n) := sorry

/-- Precomposition on fixed-degree Hom-complex cochains is additive. -/
theorem homComplexPrecomp_map_add
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain M I n) :
    (CochainComplex.HomComplex.Cochain.ofHom f).comp (z + z') (zero_add n) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n) +
        (CochainComplex.HomComplex.Cochain.ofHom f).comp z' (zero_add n) := sorry

/-- Precomposition with a cochain-complex morphism as an additive map on fixed-degree cochains. -/
noncomputable def homComplexPrecompAddMonoidHom
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain M I n →+
      CochainComplex.HomComplex.Cochain L I n where
  toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
  map_zero' := homComplexPrecomp_map_zero f n
  map_add' := homComplexPrecomp_map_add f n

/-- Evaluation of the fixed-degree precomposition map is composition with the zero cochain of
`f`. -/
@[simp] theorem homComplexPrecompAddMonoidHom_apply
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain M I n) :
    homComplexPrecompAddMonoidHom (f := f) (I := I) n z =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n) := sorry

/-- The component formula for fixed-degree Hom-complex precomposition. -/
@[simp] theorem homComplexPrecompAddMonoidHom_v
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain M I n) (p q : ℤ) (hpq : p + n = q) :
    (homComplexPrecompAddMonoidHom (f := f) (I := I) n z).v p q hpq =
      f.f p ≫ z.v p q hpq := sorry

/-- The fixed-degree precomposition maps commute with the Hom-complex differential. -/
theorem homComplexPrecomp_comm
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) i) ≫
        (CochainComplex.HomComplex L I).d i j =
      (CochainComplex.HomComplex M I).d i j ≫
        AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) j) := sorry

/-- Precomposition with a cochain-complex morphism as a chain map between Hom complexes. -/
@[stacks 079L "Hom-complex precomposition"]
noncomputable def homComplexPrecomp
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) :
    CochainComplex.HomComplex M I ⟶ CochainComplex.HomComplex L I where
  f n := AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) n)
  comm' := homComplexPrecomp_comm (f := f)

/-- The degree-`n` component of `homComplexPrecomp` is the fixed-degree precomposition map. -/
@[simp] theorem homComplexPrecomp_f
    {L M I : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) :
    (homComplexPrecomp (f := f) (I := I)).f n =
      AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) n) := sorry

/-- Hom-complex precomposition is contravariantly functorial under composition of source maps. -/
theorem homComplexPrecomp_comp
    {L M N I : CochainComplex C ℤ} (f : L ⟶ M) (g : M ⟶ N) :
    homComplexPrecomp (f := f ≫ g) (I := I) =
      homComplexPrecomp (f := g) (I := I) ≫ homComplexPrecomp (f := f) (I := I) := sorry

/-- Precomposition by the identity is the identity of the Hom complex. -/
@[simp] theorem homComplexPrecomp_id
    {L I : CochainComplex C ℤ} :
    homComplexPrecomp (f := 𝟙 L) (I := I) = 𝟙 (CochainComplex.HomComplex L I) := sorry

end CategoryTheory.CochainComplex
