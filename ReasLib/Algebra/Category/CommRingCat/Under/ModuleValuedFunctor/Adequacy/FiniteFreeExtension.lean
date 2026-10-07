module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FlatBaseChange
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.WeightGrading

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-- Given a finite-free kernel presentation of a module-valued functor, every morphism
from the kernel to a tensor-extension functor extends across the middle finite-free module. -/
theorem existsFiniteFreeExtension {A : CommRingCat.{u}} {n m : ℕ}
    {L : ModuleValuedFunctor.bundled.{u, u} A}
    (f : ModuleCat.of A (Fin n → A) ⟶ ModuleCat.of A (Fin m → A))
    (i : L ⟶ (tensorExtensionFunctor A).obj (ModuleCat.of A (Fin n → A)))
    (hi : i ≫ (tensorExtensionFunctor A).map f =
      ((bundledHasZeroMorphisms.{u, u} A).zero L
        ((tensorExtensionFunctor A).obj (ModuleCat.of A (Fin m → A)))).zero)
    (h_exact : Nonempty (IsLimit
      (@KernelFork.ofι _ _ (bundledHasZeroMorphisms.{u, u} A) _ _ _ _ i hi)))
    (M : ModuleCat.{u} A) (φ : L ⟶ (tensorExtensionFunctor A).obj M) :
    ∃ g : ModuleCat.of A (Fin n → A) ⟶ M,
      i ≫ (tensorExtensionFunctor A).map g = φ := sorry

end ModuleValuedFunctor
