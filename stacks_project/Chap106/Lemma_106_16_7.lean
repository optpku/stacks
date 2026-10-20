module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap106.Lemma_106_16_6_TensorPullback

/-!
# Reconstruction of morphisms from right exact tensor functors

A right exact coproduct-preserving tensor functor on quasi-coherent modules of
a Noetherian algebraic stack with affine diagonal is the affine tensor pullback
of a unique morphism from an affine scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Compatibility of an isomorphism `t : F ≅ tensorPullback f` with the tensor
and unit constraints of `F` and of `f*`. -/
def IsTensorPullbackIso {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤))
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅
        ModuleCat.of Γ(U.left, ⊤) (F.obj M ⊗[Γ(U.left, ⊤)] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f : GroupoidsOver.slice U ⟶ X} (t : F ≅ tensorPullback f) : Prop :=
  (∀ M N : QCoh X,
      (h_tensor M N).hom ≫
          ModuleCat.ofHom
              (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
            tensorPullback_tensorInv f M N =
        t.hom.app (tensor M N)) ∧
    t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f).hom = h_unit.hom

/-- Tensor-naturality of `t` against `h_tensor` and `h_unit` is the tensor square
with `tensorPullback_tensorInv` together with the unit square. -/
theorem IsTensorPullbackIso.iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤))
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅
        ModuleCat.of Γ(U.left, ⊤) (F.obj M ⊗[Γ(U.left, ⊤)] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f : GroupoidsOver.slice U ⟶ X} (t : F ≅ tensorPullback f) :
    IsTensorPullbackIso F h_tensor h_unit t ↔
      (∀ M N : QCoh X,
          (h_tensor M N).hom ≫
              ModuleCat.ofHom
                  (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
                tensorPullback_tensorInv f M N =
            t.hom.app (tensor M N)) ∧
        t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f).hom =
          h_unit.hom :=
  sorry

/-- Lemma 106.16.7. Let `X` be a Noetherian algebraic stack with affine
diagonal. Let `B` be a ring. Let `F : QCoh(O_X) ⥤ ModuleCat B` be a right
exact tensor functor which commutes with direct sums. Then `F` comes from a
unique morphism `Spec(B) ⟶ X`. -/
@[stacks 0GRQ]
theorem existsUnique_hom_of_rightExactTensor
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤))
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅
        ModuleCat.of Γ(U.left, ⊤) (F.obj M ⊗[Γ(U.left, ⊤)] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) :
    ∃ (f : GroupoidsOver.slice U ⟶ X) (t : F ≅ tensorPullback f),
      IsTensorPullbackIso F h_tensor h_unit t ∧
        ∀ (f' : GroupoidsOver.slice U ⟶ X) (t' : F ≅ tensorPullback f'),
          IsTensorPullbackIso F h_tensor h_unit t' →
            ∃ α : f ⟶ f', t ≪≫ tensorPullbackIso α = t' :=
  sorry

/-- Two realizing morphisms of a right exact tensor functor are related by a
2-arrow inducing the given tensor comparison. -/
theorem existsUnique_hom_of_rightExactTensor_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (F : QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤))
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅
        ModuleCat.of Γ(U.left, ⊤) (F.obj M ⊗[Γ(U.left, ⊤)] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f f' : GroupoidsOver.slice U ⟶ X}
    (t : F ≅ tensorPullback f) (t' : F ≅ tensorPullback f')
    (ht : IsTensorPullbackIso F h_tensor h_unit t)
    (ht' : IsTensorPullbackIso F h_tensor h_unit t') :
    ∃ α : f ⟶ f', t ≪≫ tensorPullbackIso α = t' :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
