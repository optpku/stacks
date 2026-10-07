module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension.Support.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

/- Remark 36.13.12: the supported retract extension can be chosen so that the map
from `P` to its restriction induces an isomorphism on cohomology sheaves in every
degree strictly above any prescribed cutoff. -/
@[stacks 09IN]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_supported_retract_extension_isIso_above :
    ∀ {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
      (P : RingedSpace.ModuleDerived U.toRingedSpace)
      (hP : RingedSpace.ModuleDerived.IsPerfect P)
      (hP_support : RingedSpace.ModuleDerived.IsSupportedOn P (j.base ⁻¹' (T : Set X)))
      (α : P ⟶ (exactPullback j.toShHom).mapDerivedCategory.obj E.obj) (a : ℤ),
      ∃ (R : RingedSpace.ModuleDerived X.toRingedSpace)
        (hR : RingedSpace.ModuleDerived.IsPerfect R)
        (hR_support : RingedSpace.ModuleDerived.IsSupportedOn R (T : Set X))
        (β : R ⟶ E.obj)
        (r : CategoryTheory.Retract P
          ((exactPullback j.toShHom).mapDerivedCategory.obj R)),
        r.i ≫ (exactPullback j.toShHom).mapDerivedCategory.map β = α ∧
          ∀ i : ℤ, a < i →
            IsIso (RingedSpace.ModuleDerived.cohomologySheafMap r.i i))
