/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Retract
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A perfect derived module supported over the pullback of a closed subset along a
quasi-compact open immersion into an affine scheme admits a perfect extension supported on
that closed subset whose restriction is the biproduct of the module with its shift. -/
@[stacks 08EK]
theorem exists_supported_biprod_shift_extension {X U : Scheme.{u}} [IsAffine X]
    (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : RingedSpace.ModuleDerived U.toRingedSpace)
    (hF : RingedSpace.ModuleDerived.IsPerfect F)
    (hF_support : RingedSpace.ModuleDerived.IsSupportedOn F (j.base ⁻¹' (T : Set X))) :
    ∃ (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (e : (exactPullback j.toShHom).mapDerivedCategory.obj E ≅ F ⊞ F⟦(1 : ℤ)⟧),
      RingedSpace.ModuleDerived.IsPerfect E ∧
        RingedSpace.ModuleDerived.IsSupportedOn E (T : Set X) := sorry

/-- A map from a perfect derived module supported over the pullback of a closed subset
along a quasi-compact open immersion extends from a retract of the restriction of a
globally perfect derived module supported on that closed subset. -/
theorem exists_supported_retract_extension {X U : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (P : RingedSpace.ModuleDerived U.toRingedSpace)
    (hP : RingedSpace.ModuleDerived.IsPerfect P)
    (hP_support : RingedSpace.ModuleDerived.IsSupportedOn P (j.base ⁻¹' (T : Set X)))
    (α : P ⟶ (exactPullback j.toShHom).mapDerivedCategory.obj E.obj) :
    ∃ (R : RingedSpace.ModuleDerived X.toRingedSpace)
      (hR : RingedSpace.ModuleDerived.IsPerfect R)
      (hR_support : RingedSpace.ModuleDerived.IsSupportedOn R (T : Set X))
      (β : R ⟶ E.obj)
      (r : CategoryTheory.Retract P
        ((exactPullback j.toShHom).mapDerivedCategory.obj R)),
      r.i ≫ (exactPullback j.toShHom).mapDerivedCategory.map β = α := sorry

/-- A perfect derived module on a quasi-compact open subscheme of a quasi-compact,
quasi-separated scheme is a retract of the restriction of a globally perfect derived
module. -/
theorem exists_retract_extension_of_isPerfect {X U : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (P : RingedSpace.ModuleDerived U.toRingedSpace)
    (hP : RingedSpace.ModuleDerived.IsPerfect P) :
    ∃ R : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect R ∧
        Nonempty (CategoryTheory.Retract P
          ((exactPullback j.toShHom).mapDerivedCategory.obj R)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
