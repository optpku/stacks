module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube
public import ReasLib.AlgebraicGeometry.GroupScheme.MulBy
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Power
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Pullback along multiplication maps of abelian varieties
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped AbelianVariety CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AbelianVariety

/-- Pullback along multiplication by `n` acts on the Picard class of an invertible module by
the quadratic combination of that class and its pullback along inversion. -/
theorem picardPullback_mulBy {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
    [AbelianVariety A] (L : A.left.Modules) [Scheme.Modules.Invertible L] (n : ℕ) :
    Scheme.Hom.picardPullback ([n]ₐ A) (Scheme.Modules.picardClass L) =
      Scheme.Modules.picardClass (RingedSpace.TensorPower.sheaf L (n * (n + 1) / 2)) +
        Scheme.Modules.picardClass
          (RingedSpace.TensorPower.sheaf
            ((Scheme.Modules.pullback (ι[A].left)).obj L) (n * (n - 1) / 2)) := sorry

/-- Pullback of an invertible module along multiplication by `n` is isomorphic to the tensor
product of the prescribed powers of the module and its pullback along inversion. -/
theorem mulByPullbackIso {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
    [AbelianVariety A] (L : A.left.Modules) [Scheme.Modules.Invertible L] (n : ℕ) :
    Nonempty
      ((Scheme.Modules.pullback ([n]ₐ A)).obj L ≅
        RingedSpace.TensorPower.sheaf L (n * (n + 1) / 2) ⊗
          RingedSpace.TensorPower.sheaf
            ((Scheme.Modules.pullback (ι[A].left)).obj L) (n * (n - 1) / 2)) := sorry

end AlgebraicGeometry.AbelianVariety
