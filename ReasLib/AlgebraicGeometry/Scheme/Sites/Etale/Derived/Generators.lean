/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.SingleFunctor.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.FiniteSum
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
  (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- A constructible degree-`b` étale cohomology sheaf admits an affine finite extension-by-zero
sum mapping to its derived object whose induced degree-`b` homology map is epimorphic. -/
theorem exists_affineFiniteSum_shift_epi
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (b : ℤ)
    (hHb : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{v} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) b).obj K)) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (j : ∀ i, U i ⟶ X)
      (hEtale : ∀ i, Etale (j i))
      (hAff : ∀ i, IsAffine (U i))
      (hKan : ∀ i, ∀ G : (U i).Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (@etaleRestriction (U i) X (j i) (hEtale i)).op.HasLeftKanExtension G)
      (hSh : ∀ i, HasWeakSheafify (U i).smallEtaleTopology (ModuleCat.{v} Λ))
      (hCoprod : HasCoproduct fun k : Fin n ↦
        (moduleExtensionByZero (j k)).obj
          ((constantSheaf (U k).smallEtaleTopology (ModuleCat.{v} Λ)).obj (.of Λ Λ))),
      ∃ (φ :
            ((DerivedCategory.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) 0).obj
              (@finiteExtensionByZeroSum X Λ _ n U j hEtale hKan inferInstance hSh hCoprod))⟦-b⟧ ⟶ K),
        Epi (CategoryTheory.DerivedCategory.homologyMapOfShiftedSingle
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) φ) := sorry

end AlgebraicGeometry.Scheme.Etale.Derived
