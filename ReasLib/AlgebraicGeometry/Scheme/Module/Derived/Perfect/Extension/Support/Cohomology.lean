/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A supported perfect extension of a perfect derived module on a quasi-compact open
subscheme can be chosen so that the retract inclusion induces an isomorphism on
cohomology sheaves in every degree strictly above a prescribed cutoff. -/
theorem exists_supported_retract_extension_isIso_above {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (P : RingedSpace.ModuleDerived U.toRingedSpace)
    (hP : RingedSpace.ModuleDerived.IsPerfect P)
    (hP_support : RingedSpace.ModuleDerived.IsSupportedOn P (j.base ⁻¹' (T : Set X)))
    (α : P ⟶ (exactPullback j.toShHom).mapDerivedCategory.obj E.obj) (a : ℤ) :
    ∃ (R : RingedSpace.ModuleDerived X.toRingedSpace)
      (hR : RingedSpace.ModuleDerived.IsPerfect R)
      (hR_support : RingedSpace.ModuleDerived.IsSupportedOn R (T : Set X))
      (β : R ⟶ E.obj)
      (r : CategoryTheory.Retract P
        ((exactPullback j.toShHom).mapDerivedCategory.obj R)),
      r.i ≫ (exactPullback j.toShHom).mapDerivedCategory.map β = α ∧
        ∀ i : ℤ, a < i →
          IsIso (RingedSpace.ModuleDerived.cohomologySheafMap r.i i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
