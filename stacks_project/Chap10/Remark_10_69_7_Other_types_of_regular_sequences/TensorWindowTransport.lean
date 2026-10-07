module

public import stacks_project.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.FinConsExteriorSplit

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degree `0`, every
tensorized Koszul complex canonically identifies with the coefficient module. -/
noncomputable def koszul_tensor_degree_zero_iso {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ} (f : Fin m → A) :
    ((HomologicalComplex.tensorObj (koszulComplexOn f)
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) ≅
      ModuleCat.of A M :=
  (tensor_single₀_X_iso_tensorRight (K := koszulComplexOn f) (M := M) 0) ≪≫
    (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
      (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin m → A)))) ≪≫
    (λ_ (ModuleCat.of A M))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): adjoining a head element does
not change the degree-`0` term of the tensorized Koszul complex. -/
noncomputable def fin_cons_tensor_degree_zero_iso_tail {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ} {r : A}
    (g : Fin (m + 1) → A) :
    ((HomologicalComplex.tensorObj (koszulComplexOn (Fin.cons r g))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) ≅
      ((HomologicalComplex.tensorObj (koszulComplexOn g)
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X 0) :=
  (koszul_tensor_degree_zero_iso (M := M) (f := Fin.cons r g)) ≪≫
    (koszul_tensor_degree_zero_iso (M := M) (f := g)).symm

#check @Function.Exact.iff_of_ladder_linearEquiv
#check @koszul_tensor_degree_zero_iso
#check @fin_cons_tensor_degree_zero_iso_tail

end RingTheory.Sequence
