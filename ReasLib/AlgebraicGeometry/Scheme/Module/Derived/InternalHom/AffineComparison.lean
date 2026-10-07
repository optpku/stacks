module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Affine comparison for derived internal Hom

This file constructs the comparison from affine tilde of a derived Hom to the derived
internal Hom of affine-tilde objects and records its finiteness criteria for invertibility.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- The exact derived affine-tilde functor from `D(A)` to derived modules on `Spec(A)`. -/
noncomputable abbrev affineTildeDerived (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace :=
  -- Local instance justification (search instability): affine-tilde Additive synthesis is unreliable after specializing `CommRingCat.of A`.
  letI : (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).Additive :=
    let hTildeLeft :
        (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).IsLeftAdjoint :=
      (AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
    let hTildeZero :
        (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
      @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _
        (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) hTildeLeft
    let hTildeCoproducts :
        PreservesColimitsOfShape (Discrete WalkingPair)
          (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
      (AlgebraicGeometry.tilde.adjunction
        (R := CommRingCat.of A)).leftAdjoint_preservesColimits.preservesColimitsOfShape
    let hTildeBiproducts :
        PreservesBinaryBiproducts
          (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
      @preservesBinaryBiproducts_of_preservesBinaryCoproducts
        _ _ _ _ _ _ (AlgebraicGeometry.tilde.functor (CommRingCat.of A))
          hTildeZero hTildeCoproducts
    @Functor.additive_of_preservesBinaryBiproducts
      _ _ _ _ _ _ (AlgebraicGeometry.tilde.functor (CommRingCat.of A))
        inferInstance hTildeZero hTildeBiproducts
  -- Local instance justification (search instability): explicitly specialize the canonical finite-limit preservation instance at `CommRingCat.of A`.
  letI : PreservesFiniteLimits
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of A)
  -- Local instance justification (search instability): explicitly specialize the canonical finite-colimit preservation instance at `CommRingCat.of A`.
  letI : PreservesFiniteColimits
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteColimits (CommRingCat.of A)
  (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).mapDerivedCategory

/-- The canonical comparison from affine tilde of `RHom_A(K, L)` to the derived internal Hom of
the affine-tilde objects. -/
noncomputable def affineComparison {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison (affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (affineTildeDerived A).obj (RHom.obj K L) ⟶
      (ihomOf H ((affineTildeDerived A).obj K)).obj
        ((affineTildeDerived A).obj L) :=
  (affineTildeDerived A).map (M.objIso K L).hom ≫
    comparisonApp M.closed H (affineTildeDerived A) T K L

/-- For a pseudo-coherent source and bounded-below target, the affine-tilde comparison for
derived internal Hom is an isomorphism. -/
theorem affineComparison_isIso_of_pseudoCoherent {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison (affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : K.IsPseudoCoherent) (hL : DerivedCategory.IsBoundedBelow L) :
    IsIso (affineComparison M H T K L) := sorry

/-- For a perfect source and arbitrary target, the affine-tilde comparison for derived
internal Hom is an isomorphism. -/
theorem affineComparison_isIso_of_perfect {A : Type u} [CommRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison (affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (hK : K.IsPerfect) :
    IsIso (affineComparison M H T K L) := sorry

/-- Over a Noetherian commutative ring, the affine-tilde comparison for derived internal Hom
is an isomorphism when the source has finite homology in every degree and the target has finite
injective dimension. -/
theorem affineComparison_isIso_of_finiteCohomology_finiteInjectiveDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [@RHom.Has.{u, u} A _]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (M : @RHom.BifunctorComparison A _ _ _)
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (T : Functor.TensorComparison (affineTildeDerived A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hL : L.HasFiniteInjectiveDimension) :
    IsIso (affineComparison M H T K L) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
