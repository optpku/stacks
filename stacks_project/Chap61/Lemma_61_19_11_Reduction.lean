module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Reduction

/-!
# Derived reduction of pro-étale module complexes modulo ideal powers

This source-facing file retains typed checks for the reusable pro-étale
coefficient-change and ideal-power reduction API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open ComplexShape

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

section ChangeOfRings
variable {Λ Λ' : Type v} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
variable (X : Scheme.{u})
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]

#check (proEtModuleExtendScalars φ X :
  Sheaf (ProEt.topology X) (ModuleCat.{v} Λ) ⥤
    Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))

#check (proEtModuleExtendScalars_def φ X :
  proEtModuleExtendScalars φ X =
    sheafToPresheaf (ProEt.topology X) (ModuleCat.{v} Λ) ⋙
      DerivedColimit.ChangeOfRings.presheafExtendScalars.{u + 1, u, v, v, 0} φ ⋙
      presheafToSheaf (ProEt.topology X) (ModuleCat.{v} Λ'))

variable [(ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars φ)]

#check (proEtModuleRestrictScalars φ X :
  Sheaf (ProEt.topology X) (ModuleCat.{v} Λ') ⥤
    Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))

#check (proEtModuleRestrictScalars_def φ X :
  proEtModuleRestrictScalars φ X =
    sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars φ))

variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))]
variable [(proEtModuleExtendScalars φ X).Additive]
variable [(Functor.Homotopy.toDerived (proEtModuleExtendScalars φ X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))]

#check (proEtDerivedExtendScalars φ X :
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) ⥤
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ')))

#check (proEtDerivedExtendScalars_def φ X :
  proEtDerivedExtendScalars φ X =
    Functor.LeftDerived.Homotopy.functor (proEtModuleExtendScalars φ X))

variable [(proEtModuleRestrictScalars φ X).Additive]
variable [PreservesFiniteLimits (proEtModuleRestrictScalars φ X)]
variable [PreservesFiniteColimits (proEtModuleRestrictScalars φ X)]

#check (proEtDerivedRestrictScalars φ X :
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ')) ⥤
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)))

#check (proEtDerivedRestrictScalars_def φ X :
  proEtDerivedRestrictScalars φ X =
    (proEtModuleRestrictScalars φ X).mapDerivedCategory)

end ChangeOfRings

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable (I : Ideal Λ) (n : ℕ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n)))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))]
variable (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)))

#check (proEtReduction I n K :
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))))

#check (proEtReduction_eq I n K :
  proEtReduction I n K =
    (proEtDerivedExtendScalars (Ideal.Quotient.mk (I ^ n)) X).obj K)

variable [(ProEt.topology X).HasSheafCompose
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)))]
variable [(proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
variable [PreservesFiniteLimits
  (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)]
variable [PreservesFiniteColimits
  (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)]

#check (proEtReduction_restrictScalars I n K :
  (proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
      (proEtReduction I n K) =
    (proEtDerivedExtendScalars (Ideal.Quotient.mk (I ^ n)) X ⋙
      proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj K)

end AlgebraicGeometry.Scheme

end

end
