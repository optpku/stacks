module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.CodimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.DenseOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform

/-!
# Flattening strict transforms by admissible blowups

This module records a local-to-global existence theorem for flattening strict transforms after
admissible blowups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite compatible pair of jointly surjective étale families carrying admissible blowups
that flatten the local strict transforms yields an admissible blowup that flattens the global
strict transform. -/
theorem exists_isAdmissibleBlowup_flattening_of_etaleCover
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : S.Opens) [QuasiCompact U.ι] {n : ℕ}
    (Sᵢ Xᵢ Sᵢ' : Fin n → Scheme.{u})
    (eᵢ : ∀ i, Sᵢ i ⟶ S) (jᵢ : ∀ i, Xᵢ i ⟶ X)
    (fᵢ : ∀ i, Xᵢ i ⟶ Sᵢ i) (bᵢ : ∀ i, Sᵢ' i ⟶ Sᵢ i)
    (Iᵢ : ∀ i, (Sᵢ i).IdealSheafData)
    [∀ i, QuasiCompact (eᵢ i)] [∀ i, Etale (eᵢ i)] [∀ i, Etale (jᵢ i)]
    (sq : ∀ i, CommSq (jᵢ i) (fᵢ i) f (eᵢ i))
    (hS : ∀ s : S, ∃ i, s ∈ Set.range (eᵢ i))
    (hX : ∀ x : X, ∃ i, x ∈ Set.range (jᵢ i))
    [∀ i, IsAdmissibleBlowupCenter ((eᵢ i) ⁻¹ᵁ U) (bᵢ i) (Iᵢ i)]
    (hflat : ∀ i, flatOver
      (strictTransformModule (bᵢ i) ((Iᵢ i).comap (bᵢ i)) (fᵢ i)
        ((Scheme.Modules.pullback (jᵢ i)).obj ℱ))
      (pullback.snd (fᵢ i) (bᵢ i))) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        flatOver (strictTransformModule b (I.comap b) f ℱ) (pullback.snd f b) := sorry

/-- For an affine, finitely presented, flat morphism with geometrically integral fibres, a
finite-type quasicoherent module that is finitely presented and flat in codimension zero over a
quasi-compact open becomes finite locally free on a surjective open of its strict transform after
an admissible blowup. -/
theorem exists_isAdmissibleBlowup_finiteLocallyFreeOpen
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsAffineHom f] [Scheme.Hom.FinitePresentation f]
    [Flat f] [GeometricallyIntegral f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (U : S.Opens) [QuasiCompact U.ι]
    [(ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation]
    (hflat :
      flatOverInCodimensionZero
        (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U)) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
        IsAdmissibleBlowupCenter U b I ∧
        ∃ V : (strictTransformAmbient b f).Opens,
          ((strictTransformModule b (I.comap b) f ℱ).restrict V.ι).IsFiniteLocallyFree ∧
            Surjective (V.ι ≫ pullback.snd f b) := sorry

/-- A finite-type quasicoherent module that is finitely presented and flat over a quasi-compact
open admits an admissible blowup whose strict transform is finitely presented and flat over the
new base. -/
theorem exists_isAdmissibleBlowup_flattening
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (U : S.Opens) [QuasiCompact U.ι]
    [(ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation]
    (h_flat : flatOver (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U)) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        let ℱ' := strictTransformModule b (I.comap b) f ℱ
        ℱ'.IsFinitePresentation ∧ flatOver ℱ' (pullback.snd f b) := sorry

end AlgebraicGeometry.Scheme.Modules
