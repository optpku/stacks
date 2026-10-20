/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

namespace etaleDerivedLowerShriek

/-- For a finite type separated morphism of quasi-compact quasi-separated
schemes and a torsion coefficient ring, the derived lower shriek functor
`etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat Λ))`
associated to the compactification `P` admits a right adjoint. -/
instance isLeftAdjoint [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΛ : AddMonoid.IsTorsion Λ) :
    let _ := hΛ
    (etaleDerivedLowerShriek X P :
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).IsLeftAdjoint := sorry

/-- For torsion coefficients, compactification-derived lower shriek admits a right adjoint. -/
instance isLeftAdjointOfTorsion [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [hΛ : Fact (AddMonoid.IsTorsion Λ)] :
    (etaleDerivedLowerShriek X P :
      DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).IsLeftAdjoint :=
  isLeftAdjoint X P hΛ.out

end etaleDerivedLowerShriek

variable (Λ)
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [((etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).IsLeftAdjoint]

/-- The derived upper shriek `Rf^!`, the chosen right adjoint of
`etaleDerivedLowerShriek`. -/
def etaleDerivedUpperShriek : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) :=
  (etaleDerivedLowerShriek X P).rightAdjoint

/-- Derived upper shriek is the chosen right adjoint of `Rf_!`. -/
theorem etaleDerivedUpperShriek_def :
    etaleDerivedUpperShriek X Λ P = (etaleDerivedLowerShriek X P).rightAdjoint :=
  sorry

/-- The adjunction `Rf_! ⊣ Rf^!` on unbounded derived categories of étale
`Λ`-modules. -/
def etaleDerivedLowerShriekAdjunction :
    etaleDerivedLowerShriek X P ⊣ etaleDerivedUpperShriek X Λ P :=
  Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P)

/-- The hom-equivalence of the derived compact-support adjunction. -/
def etaleDerivedLowerShriekAdjunction_homEquiv
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    ((etaleDerivedLowerShriek X P).obj L ⟶ K) ≃
      (L ⟶ (etaleDerivedUpperShriek X Λ P).obj K) :=
  (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K


end AlgebraicGeometry.Scheme.Etale

end
