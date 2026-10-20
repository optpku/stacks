/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalityObstruction
import StacksCheckRecall

/-!
# First-order thickenings detecting failure of versality

The shared obstruction theorem is checked below with its source-facing type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The skyscraper module sheaf on the target of `i` with value `κ(i.base u)` at
the image of `u`. -/
def residueFieldSkyscraper {U T : Scheme.{u}} (i : U ⟶ T) (u : U) :
    RingedSpace.Modules T.toRingedSpace :=
  Scheme.Modules.residueFieldSkyscraper (i.base u)

/-- The morphism in `Over S` associated to a scheme morphism over `S`. -/
def overHom {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    (i : U ⟶ T) (hi : i ≫ hT = hU) :
    Over.mk hU ⟶ Over.mk hT :=
  Over.homMk i hi

/-- The morphism in `Over S` induced by an open immersion of the source of
`hT`. -/
def openOverHom {S T : Scheme.{u}} (hT : T ⟶ S) (W : T.Opens) :
    Over.mk (W.ι ≫ hT) ⟶ Over.mk hT :=
  Over.homMk W.ι rfl

/-- The morphism in `Over S` induced by restricting `i` to an open of the
target. -/
def restrictOpenOverHom {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    {i : U ⟶ T} (hi : i ≫ hT = hU) (W : T.Opens) :
    Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk (W.ι ≫ hT) :=
  Over.homMk (i ∣_ W) (by
    change (i ∣_ W) ≫ (W.ι ≫ hT) = (i ⁻¹ᵁ W).ι ≫ hU
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi])

/- Lemma 98.19.1: failure of versality is detected by a first-order thickening
with residue-field kernel and no local retraction. -/
@[stacks 0G2J] #check
  (AlgebraicGeometry.GroupoidsOver.exists_firstOrderThickening_of_not_isVersalAt :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : U) [IsFiniteTypePoint u]
    (h : ¬ IsVersalAt hU x hx u),
    ∃ (T : Scheme.{u}) (hT : T ⟶ S) (i : U ⟶ T) (hi : i ≫ hT = hU)
      (y : X.total) (hy : X.p.obj y = Over.mk hT) (φ : x ⟶ y),
      X.p.IsHomLift (overHom i hi) φ ∧
        IsFirstOrderThickening i ∧
        Nonempty (i.ker.toModule ≅ residueFieldSkyscraper i u) ∧
        ¬ ∃ (W : T.Opens), i.base u ∈ W ∧
          ∃ (β : (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1 ⟶ x)
            (ρ : (Chosen.reindexObj X.p (openOverHom hU (i ⁻¹ᵁ W)) ⟨x, hx⟩).1 ⟶
                (Chosen.reindexObj X.p (openOverHom hT W) ⟨y, hy⟩).1),
              X.p.IsHomLift (restrictOpenOverHom hi W) ρ ∧
                ρ ≫ Chosen.cartesianHom X.p (openOverHom hT W) ⟨y, hy⟩ =
                    Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W))
                      ⟨x, hx⟩ ≫ φ ∧
                  ρ ≫ β =
                    Chosen.cartesianHom X.p (openOverHom hU (i ⁻¹ᵁ W))
                      ⟨x, hx⟩)

end AlgebraicGeometry.GroupoidsOver
