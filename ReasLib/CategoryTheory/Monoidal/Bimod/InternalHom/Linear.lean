module

public import ReasLib.CategoryTheory.Adjunction.Linear
public import ReasLib.CategoryTheory.Monoidal.Bimod.InternalHom.Preadditive
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear relative internal Hom functors of bimodules

Relative internal Hom with a fixed bimodule source is linear in its target. This is the generic
right-adjoint counterpart to linear fixed-source balanced tensor product.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w u v

namespace CategoryTheory.Bimod.InternalHom

variable {k : Type w} [Semiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
variable [MonoidalCategory C] [monoidalPreadditive : MonoidalPreadditive C]
variable [monoidalLinear : MonoidalLinear k C]
variable [hasEqualizers : HasEqualizers C] [hasCoequalizers : HasCoequalizers C]
variable [preservesTensorLeft :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [preservesTensorRight :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A B : Mon C}

include monoidalPreadditive monoidalLinear hasEqualizers hasCoequalizers
  preservesTensorLeft preservesTensorRight

/-- Relative internal Hom with fixed source is `k`-linear in its target module. -/
@[stacks 0FR6 "linear relative internal Hom functor"]
instance functorLinear (H : RightInternalHom C) (N : Bimod A B) :
    Functor.Linear k (functor H N) := sorry

/-- Relative internal-Hom postcomposition preserves scalar multiples of module morphisms. -/
@[simp]
theorem map_smul (H : RightInternalHom C) (N : Bimod A B) (r : k)
    {L L' : RightModule B} (f : L ⟶ L') :
    map H N (r • f) = r • map H N f := sorry

variable (H : RightInternalHom C) (N : Bimod A B)

#synth Functor.Linear k (functor H N)

end CategoryTheory.Bimod.InternalHom

end
