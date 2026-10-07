module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.ChangeOfRings
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

/-!
# Derived reduction of pro-étale module complexes modulo ideal powers

Extension of scalars on sheaves of modules on `X.ProEt` is sheafification of
pointwise `ModuleCat.extendScalars`. The total left derived functor along
`Ideal.Quotient.mk (I ^ n)` is the reduction `K ↦ K_n` in
`D(X.ProEt, Λ ⧸ I ^ n)`. Restriction of scalars of this object is derived
extend-then-restrict along `Ideal.Quotient.mk (I ^ n)`.
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

/-- Extension of scalars on pro-étale sheaves of modules along `φ`, obtained by
pointwise `ModuleCat.extendScalars` followed by sheafification. -/
def proEtModuleExtendScalars (X : Scheme.{u})
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ')] :
    Sheaf (ProEt.topology X) (ModuleCat.{v} Λ) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{v} Λ') :=
  sheafToPresheaf (ProEt.topology X) (ModuleCat.{v} Λ) ⋙
    DerivedColimit.ChangeOfRings.presheafExtendScalars.{u + 1, u, v, v, 0} φ ⋙
    presheafToSheaf (ProEt.topology X) (ModuleCat.{v} Λ')

/-- Underived pro-étale extension of scalars sheafifies whiskered
`ModuleCat.extendScalars`. -/
theorem proEtModuleExtendScalars_def (X : Scheme.{u})
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ')] :
    proEtModuleExtendScalars φ X =
      sheafToPresheaf (ProEt.topology X) (ModuleCat.{v} Λ) ⋙
        DerivedColimit.ChangeOfRings.presheafExtendScalars.{u + 1, u, v, v, 0} φ ⋙
        presheafToSheaf (ProEt.topology X) (ModuleCat.{v} Λ') :=
  sorry

/-- Restriction of scalars on pro-étale sheaves of modules along `φ`. -/
abbrev proEtModuleRestrictScalars (X : Scheme.{u})
    [(ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars φ)] :
    Sheaf (ProEt.topology X) (ModuleCat.{v} Λ') ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{v} Λ) :=
  sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars φ)

/-- Restriction of scalars of pro-étale sheaves is `sheafCompose` of
`ModuleCat.restrictScalars`. -/
theorem proEtModuleRestrictScalars_def (X : Scheme.{u})
    [(ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars φ)] :
    proEtModuleRestrictScalars φ X =
      sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars φ) :=
  sorry

/-- Derived extension of scalars `- ⊗_Λ^L Λ' : D(X.ProEt, Λ) ⥤ D(X.ProEt, Λ')`. -/
def proEtDerivedExtendScalars (X : Scheme.{u})
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))]
    [(proEtModuleExtendScalars φ X).Additive]
    [(Functor.Homotopy.toDerived (proEtModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))] :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ')) :=
  Functor.LeftDerived.Homotopy.functor (proEtModuleExtendScalars φ X)

/-- Derived pro-étale extension of scalars is the total left derived functor of the
sheaf-level extension functor. -/
theorem proEtDerivedExtendScalars_def (X : Scheme.{u})
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))]
    [(proEtModuleExtendScalars φ X).Additive]
    [(Functor.Homotopy.toDerived (proEtModuleExtendScalars φ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))] :
    proEtDerivedExtendScalars φ X =
      Functor.LeftDerived.Homotopy.functor (proEtModuleExtendScalars φ X) :=
  sorry

/-- Restriction of scalars on `D(X.ProEt, -)` along `φ`. -/
def proEtDerivedRestrictScalars (X : Scheme.{u})
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))]
    [(ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(proEtModuleRestrictScalars φ X).Additive]
    [PreservesFiniteLimits (proEtModuleRestrictScalars φ X)]
    [PreservesFiniteColimits (proEtModuleRestrictScalars φ X)] :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ')) ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) :=
  (proEtModuleRestrictScalars φ X).mapDerivedCategory

/-- Derived restriction of scalars is `mapDerivedCategory` of the sheaf-level functor. -/
theorem proEtDerivedRestrictScalars_def (X : Scheme.{u})
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ')]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ'))]
    [(ProEt.topology X).HasSheafCompose (ModuleCat.restrictScalars φ)]
    [(proEtModuleRestrictScalars φ X).Additive]
    [PreservesFiniteLimits (proEtModuleRestrictScalars φ X)]
    [PreservesFiniteColimits (proEtModuleRestrictScalars φ X)] :
    proEtDerivedRestrictScalars φ X =
      (proEtModuleRestrictScalars φ X).mapDerivedCategory :=
  sorry

end ChangeOfRings

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]

/-- Derived reduction of `K` modulo `I ^ n`, as an object of
`D(X.ProEt, Λ ⧸ I ^ n)`. -/
def proEtReduction (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))) :=
  (proEtDerivedExtendScalars (Ideal.Quotient.mk (I ^ n)) X).obj K

/-- Reduction modulo `I ^ n` is derived extension of scalars along
`Ideal.Quotient.mk (I ^ n)`. -/
theorem proEtReduction_eq (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))) :
    proEtReduction I n K =
      (proEtDerivedExtendScalars (Ideal.Quotient.mk (I ^ n)) X).obj K :=
  sorry

/-- Restriction of scalars of `proEtReduction I n K` is derived extend-then-restrict
along `Ideal.Quotient.mk (I ^ n)`. -/
theorem proEtReduction_restrictScalars (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (up ℤ))]
    [(ProEt.topology X).HasSheafCompose
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)))]
    [(proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [PreservesFiniteLimits
      (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)]
    [PreservesFiniteColimits
      (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))) :
    (proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
        (proEtReduction I n K) =
      (proEtDerivedExtendScalars (Ideal.Quotient.mk (I ^ n)) X ⋙
        proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj K :=
  sorry

end AlgebraicGeometry.Scheme

end

end
