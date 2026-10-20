/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResidueFieldSkyscraper
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- If an object of a category fibred in groupoids with (RS*) over a locally
Noetherian base is not versal at a finite type point of its affine finite-type
source, there is a first-order thickening with residue-field skyscraper kernel
whose induced object morphism admits no local retraction near that point. -/
@[stacks 0G2J]
theorem exists_firstOrderThickening_of_not_isVersalAt
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : U) [IsFiniteTypePoint u]
    (h : ¬ IsVersalAt hU x hx u) :
    ∃ (T : Scheme.{u}) (hT : T ⟶ S) (i : U ⟶ T) (hi : i ≫ hT = hU)
      (y : X.total) (hy : X.p.obj y = Over.mk hT) (φ : x ⟶ y),
      X.p.IsHomLift (Over.homMk i hi : Over.mk hU ⟶ Over.mk hT) φ ∧
        IsFirstOrderThickening i ∧
        Nonempty (i.ker.toModule ≅ Scheme.Modules.residueFieldSkyscraper (i.base u)) ∧
        ¬ ∃ (W : T.Opens), i.base u ∈ W ∧
          ∃ (β : (Chosen.reindexObj X.p
                (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1 ⟶ x)
            (ρ : (Chosen.reindexObj X.p (Over.homMk (i ⁻¹ᵁ W).ι
                      rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU) ⟨x, hx⟩).1 ⟶
                (Chosen.reindexObj X.p
                  (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩).1),
              X.p.IsHomLift (Over.homMk (i ∣_ W) (by
                change (i ∣_ W) ≫ (W.ι ≫ hT) = (i ⁻¹ᵁ W).ι ≫ hU
                rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi]) :
                  Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk (W.ι ≫ hT)) ρ ∧
                ρ ≫ Chosen.cartesianHom X.p
                    (Over.homMk W.ι rfl : Over.mk (W.ι ≫ hT) ⟶ Over.mk hT) ⟨y, hy⟩ =
                    Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι
                      rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU)
                      ⟨x, hx⟩ ≫ φ ∧
                  ρ ≫ β =
                    Chosen.cartesianHom X.p (Over.homMk (i ⁻¹ᵁ W).ι
                      rfl : Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk hU)
                      ⟨x, hx⟩ :=
  sorry

end AlgebraicGeometry.GroupoidsOver
