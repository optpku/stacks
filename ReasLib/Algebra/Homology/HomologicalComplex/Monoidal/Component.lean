module

public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homogeneous components of monoidal morphisms of complexes

This file extracts the homogeneous maps carried by morphisms out of the tensor product and tensor
unit of homological complexes.  It is the common component-level interface for monoid, module, and
bimodule objects in totalized complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace HomologicalComplex.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable {I : Type w} [AddMonoid I] [DecidableEq I]
variable {c : ComplexShape I} [c.TensorSigns]

/-- The `(i,j)`-homogeneous component of a morphism out of a tensor product of complexes. -/
@[stacks 0FRF "homogeneous tensor-morphism component"]
noncomputable def tensorHomComponent
    {K L M : HomologicalComplex C c} [K.HasTensor L]
    (f : tensorObj K L ⟶ M) (i j : I) :
    K.X i ⊗ L.X j ⟶ M.X (i + j) :=
  ιTensorObj K L i j (i + j) rfl ≫ f.f (i + j)

/-- The degree-zero component of a morphism out of the tensor-unit complex. -/
@[stacks 0FRF "tensor-unit morphism component"]
noncomputable def unitHomComponent
    {K : HomologicalComplex C c} (f : tensorUnit C c ⟶ K) :
    𝟙_ C ⟶ K.X 0 :=
  (singleObjXSelf c 0 (𝟙_ C)).inv ≫ f.f 0

/-- A morphism out of a tensor product is determined by all of its homogeneous components. -/
@[ext]
theorem tensorHom_ext
    {K L M : HomologicalComplex C c} [K.HasTensor L]
    {f g : tensorObj K L ⟶ M}
    (h : ∀ i j : I, tensorHomComponent f i j = tensorHomComponent g i j) :
    f = g := sorry

/-- A morphism out of the tensor-unit complex is determined by its degree-zero component. -/
@[ext]
theorem unitHom_ext {K : HomologicalComplex C c} {f g : tensorUnit C c ⟶ K}
    (h : unitHomComponent f = unitHomComponent g) :
    f = g := sorry

/-- Taking a homogeneous tensor component commutes with postcomposition. -/
@[reassoc]
theorem tensorHomComponent_comp
    {K L M N : HomologicalComplex C c} [K.HasTensor L]
    (f : tensorObj K L ⟶ M) (g : M ⟶ N) (i j : I) :
    tensorHomComponent (f ≫ g) i j = tensorHomComponent f i j ≫ g.f (i + j) := sorry

/-- Taking a homogeneous tensor component commutes with maps in both tensor factors. -/
@[reassoc]
theorem tensorHomComponent_tensorHom
    {K K' L L' M : HomologicalComplex C c}
    [K.HasTensor L] [K'.HasTensor L']
    (f : K ⟶ K') (g : L ⟶ L') (h : tensorObj K' L' ⟶ M) (i j : I) :
    tensorHomComponent (tensorHom f g ≫ h) i j =
      (f.f i ⊗ₘ g.f j) ≫ tensorHomComponent h i j := sorry

/-- Taking the tensor-unit component commutes with postcomposition. -/
@[reassoc]
theorem unitHomComponent_comp
    {K L : HomologicalComplex C c} (f : tensorUnit C c ⟶ K) (g : K ⟶ L) :
    unitHomComponent (f ≫ g) = unitHomComponent f ≫ g.f 0 := sorry



end HomologicalComplex.Monoidal

end
