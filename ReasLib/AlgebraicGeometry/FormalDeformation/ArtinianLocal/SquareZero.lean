/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.CommOpposite
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Square-zero extensions `k[I]` in `ArtinianLocalAlgCat`

For a finite `k`-module `I`, the trivial square-zero extension `TrivSqZeroExt k I` bundles
as the object `k[I]` of `C_Λ`, together with the canonical projection onto the residue field
`k`.
-/

@[expose] public section

open scoped Module.CommOpposite

open CategoryTheory IsLocalRing TrivSqZeroExt

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The trivial square-zero extension is a `Λ`-algebra via the composite `Λ → k → k[I]`.
Priority is below the canonical `k`-algebra instance `algebra' k k I`. -/
instance (priority := 80) instAlgebra_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    Algebra Λ (TrivSqZeroExt k I) :=
  RingHom.toAlgebra ((algebraMap k (TrivSqZeroExt k I)).comp (algebraMap Λ k))

/-- The tower `Λ → k → TrivSqZeroExt k I`. -/
instance instIsScalarTower_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    IsScalarTower Λ k (TrivSqZeroExt k I) := sorry

/-- The trivial square-zero extension of a module over a field is a local ring. -/
instance instIsLocalRing_squareZero {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalRing (TrivSqZeroExt k I) := sorry

/-- The trivial square-zero extension of a finite module over a field is Artinian. -/
instance instIsArtinianRing_squareZero {I : Type u} [AddCommGroup I] [Module k I]
    [Module.Finite k I] : IsArtinianRing (TrivSqZeroExt k I) := sorry

/-- The coefficient projection of `TrivSqZeroExt k I` is a local homomorphism. -/
instance instIsLocalHom_fstHom {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom (fstHom k k I) := sorry

/-- The coefficient projection, as a `Λ`-algebra map, is local. -/
instance instIsLocalHom_fstHom_restrict {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom ((fstHom k k I).restrictScalars Λ) := sorry

/-- The underlying ring homomorphism of the coefficient projection is local. -/
instance instIsLocalHom_fstHom_restrict_toRingHom {I : Type u} [AddCommGroup I] [Module k I] :
    IsLocalHom ((fstHom k k I).restrictScalars Λ).toRingHom := sorry

variable (Λ k)

/-- Residue-field identification of `TrivSqZeroExt k I` with `k`, via the coefficient
projection and the inclusion of scalars. -/
noncomputable def squareZeroResidueFieldIso (I : Type u) [AddCommGroup I] [Module k I] :
    ResidueField (TrivSqZeroExt k I) ≃ₐ[Λ] k :=
  AlgEquiv.ofAlgHom
    { ResidueField.lift ((fstHom k k I).restrictScalars Λ).toRingHom with
      commutes' := sorry }
    ((Ideal.Quotient.mkₐ Λ (maximalIdeal (TrivSqZeroExt k I))).comp
      ((inlAlgHom k k I).restrictScalars Λ))
    sorry sorry

/-- The residue identification of `k[I]` sends the class of a square-zero extension to its
scalar coefficient. -/
theorem squareZeroResidueFieldIso_apply (I : Type u) [AddCommGroup I] [Module k I]
    (x : TrivSqZeroExt k I) :
    squareZeroResidueFieldIso Λ k I (IsLocalRing.residue (TrivSqZeroExt k I) x) = x.fst := sorry

/-- The trivial square-zero extension `TrivSqZeroExt k I`, viewed as an object of
`ArtinianLocalAlgCat Λ k`. -/
noncomputable def squareZero (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    ArtinianLocalAlgCat Λ k :=
  of (TrivSqZeroExt k I) (squareZeroResidueFieldIso Λ k I)

/-- The bundled square-zero object has carrier `TrivSqZeroExt k I`. -/
theorem squareZero_carrier (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    (squareZero Λ k I).carrier = TrivSqZeroExt k I := sorry

/-- The canonical projection `k[I] ⟶ k` in `ArtinianLocalAlgCat`. -/
noncomputable def squareZeroToResidue (I : Type u) [AddCommGroup I] [Module k I]
    [Module.Finite k I] : squareZero Λ k I ⟶ residue Λ k :=
  Hom.of ((fstHom k k I).restrictScalars Λ)
    (instIsLocalHom_fstHom_restrict (Λ := Λ) (k := k) (I := I)) sorry

/-- The underlying algebra map of `squareZeroToResidue` is the coefficient projection. -/
theorem squareZeroToResidue_hom (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    (squareZeroToResidue Λ k I).hom = (fstHom k k I).restrictScalars Λ := sorry

/-- The projection `k[I] ⟶ k` is surjective. -/
theorem squareZeroToResidue_surjective (I : Type u) [AddCommGroup I] [Module k I]
    [Module.Finite k I] : Function.Surjective (squareZeroToResidue Λ k I).hom := sorry

/-- The projection `k[I] ⟶ k` is a local `Λ`-algebra map compatible with residue
identifications. -/
theorem squareZeroToResidue_spec (I : Type u) [AddCommGroup I] [Module k I] [Module.Finite k I] :
    IsLocalHom (squareZeroToResidue Λ k I).hom ∧
      residueCompat (squareZeroToResidue Λ k I).hom (squareZeroToResidue Λ k I).isLocalHom =
        residueIsoHom (squareZero Λ k I) := sorry

end ArtinianLocalAlgCat
