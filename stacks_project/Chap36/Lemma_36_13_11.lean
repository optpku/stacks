module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension.Support
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

/- Lemma 36.13.11: on a quasi-compact quasi-separated scheme, a map from a perfect
derived module supported on the restriction of a closed subset extends from a retract
of the restriction of a globally perfect derived module supported on that subset. -/
@[stacks 09IM]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_supported_retract_extension :
    ∀ {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
      (P : RingedSpace.ModuleDerived U.toRingedSpace)
      (hP : RingedSpace.ModuleDerived.IsPerfect P)
      (hP_support : RingedSpace.ModuleDerived.IsSupportedOn P (j.base ⁻¹' (T : Set X)))
      (α : P ⟶ (exactPullback j.toShHom).mapDerivedCategory.obj E.obj),
      ∃ (R : RingedSpace.ModuleDerived X.toRingedSpace)
        (hR : RingedSpace.ModuleDerived.IsPerfect R)
        (hR_support : RingedSpace.ModuleDerived.IsSupportedOn R (T : Set X))
        (β : R ⟶ E.obj)
        (r : CategoryTheory.Retract P
          ((exactPullback j.toShHom).mapDerivedCategory.obj R)),
        r.i ≫ (exactPullback j.toShHom).mapDerivedCategory.map β = α)
