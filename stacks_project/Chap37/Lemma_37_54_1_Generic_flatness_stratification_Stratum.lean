module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Stratum

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Modules.stratumOpen :
  {S : Scheme.{u}} → {t : ℕ} →
    (Z : Fin (t + 1) → S.IdealSheafData) → (i : Fin t) →
      (Z i.castSucc).subscheme.Opens)

#check (AlgebraicGeometry.Scheme.Modules.stratumOpen_def :
  {S : Scheme.{u}} → {t : ℕ} →
    (Z : Fin (t + 1) → S.IdealSheafData) → (i : Fin t) →
      AlgebraicGeometry.Scheme.Modules.stratumOpen Z i =
        ((Z i.succ).comap (Z i.castSucc).subschemeι).openComplement)

#check (AlgebraicGeometry.Scheme.Modules.stratumMap :
  {S : Scheme.{u}} → {t : ℕ} →
    (Z : Fin (t + 1) → S.IdealSheafData) → (i : Fin t) →
      (AlgebraicGeometry.Scheme.Modules.stratumOpen Z i).toScheme ⟶ S)

#check (AlgebraicGeometry.Scheme.Modules.stratumMap_def :
  {S : Scheme.{u}} → {t : ℕ} →
    (Z : Fin (t + 1) → S.IdealSheafData) → (i : Fin t) →
      AlgebraicGeometry.Scheme.Modules.stratumMap Z i =
        (AlgebraicGeometry.Scheme.Modules.stratumOpen Z i).ι ≫
          (Z i.castSucc).subschemeι)
