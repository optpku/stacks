module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X)
variable
  (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
  (jPush : DerivedQCoh V.toScheme ⥤ DerivedQCoh Y)
  (jPrimePush : DerivedQCoh U.toScheme ⥤ DerivedQCoh X)
  (jAdjunction : OpenImmersion.pullback V.ι ⊣ jPush)
  (jPrimeAdjunction : OpenImmersion.pullback U.ι ⊣ jPrimePush)
  (baseChangeIso :
    aV ⋙ jPrimePush ≅ jPush ⋙ a)

/-- For a quasi-compact open `V`, a right adjoint preserves support away from `V` in
the bounded-below derived category exactly when the associated open-restriction
base-change map is invertible on bounded-below objects. -/
theorem supportOnComplement_iff_isIso_boundedBelow
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V) :
    (∀ Q : DerivedQCoh Y,
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj →
      RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
      RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ) ↔
    ∀ K : DerivedQCoh Y,
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj →
      IsIso
        ((DerivedBaseChange.mapOfRight
          jAdjunction jPrimeAdjunction
          baseChangeIso.inv).app K) := sorry

/-- For a quasi-compact open `V`, a right adjoint preserves support away from `V` in
the unbounded derived category exactly when the associated open-restriction
base-change map is invertible on every object. -/
theorem supportOnComplement_iff_isIso
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V) :
    (∀ Q : DerivedQCoh Y,
      RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
      RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ) ↔
    ∀ K : DerivedQCoh Y,
      IsIso
        ((DerivedBaseChange.mapOfRight
          jAdjunction jPrimeAdjunction
          baseChangeIso.inv).app K) := sorry

/-- If a right adjoint preserves arbitrary coproducts, bounded-below support
preservation away from a quasi-compact open implies support preservation for all objects. -/
theorem supportOnComplement_of_preservesCoproducts
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V)
    (h_coproducts : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) a)
    (h_boundedBelow : ∀ Q : DerivedQCoh Y,
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj →
      RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
      RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ) :
    ∀ Q : DerivedQCoh Y,
      RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
      RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
