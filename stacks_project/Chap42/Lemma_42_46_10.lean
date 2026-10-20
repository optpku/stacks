module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ConstantRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TensorInvertible
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.TensorInvertible

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.ChernClass.Derived
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

universe u

/- Lemma 42.46.10: If a perfect derived module has constant integer virtual rank, tensoring
by an invertible module changes every Chern class by the generalized binomial formula. -/
@[stacks 0FAF]
#check (AlgebraicGeometry.ChernClass.Derived.totalClass_tensor_invertible :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E : ModuleDerived X.toRingedSpace) (L : X.Modules)
    [Scheme.Modules.Invertible L]
    (hPerfect : ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (r : ℤ) (hRank : Scheme.ModuleDerived.IsConstantRank E r) (i : ℕ),
    ChernClass.homogeneous δ π i
        (totalClass δ π classes
          (E ⊗ᴸ (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj L)
          (hPerfect.tensorInvertible L) (hDefined.tensorInvertible L) i) =
      ∑ j ∈ Finset.range (i + 1),
        (Ring.choose (r - (i : ℤ) + (j : ℤ)) j : ℤ) •
          (ChernClass.homogeneous δ π (i - j)
              (totalClass δ π classes E hPerfect hDefined (i - j)) *
            ChernClass.homogeneous δ π 1 (classes.component L 1) ^ j))
