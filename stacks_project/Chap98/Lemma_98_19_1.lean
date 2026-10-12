/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Definition_98_18_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# First-order thickenings detecting failure of versality

If an object of a category fibred in groupoids over `(Sch/S)_fppf` with (RS*)
is not versal at a finite type point of an affine finite-type source, there is a
first-order thickening whose kernel is a residue-field skyscraper and which
admits no local retraction of the corresponding fibre morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open RingedSpace.Module
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The skyscraper module sheaf on the target of `i` with value `κ(i.base u)` at
the image of `u`. -/
def residueFieldSkyscraper {U T : Scheme.{u}} (i : U ⟶ T) (u : U) :
    RingedSpace.Modules T.toRingedSpace :=
  Skyscraper.atPoint (i.base u)
    (ModuleCat.of (RingCat.of (T.presheaf.stalk (i.base u)))
      (IsLocalRing.ResidueField (T.presheaf.stalk (i.base u))))

/-- `residueFieldSkyscraper i u` is the stalk-module skyscraper of
`κ(i.base u)` on `T`. -/
theorem residueFieldSkyscraper_spec {U T : Scheme.{u}} (i : U ⟶ T) (u : U) :
    residueFieldSkyscraper i u =
      Skyscraper.atPoint (i.base u)
        (ModuleCat.of (RingCat.of (T.presheaf.stalk (i.base u)))
          (IsLocalRing.ResidueField (T.presheaf.stalk (i.base u)))) :=
  sorry

/-- Restriction of a morphism over `S` to an open of the target remains a
morphism over `S`. -/
theorem restrictOpen_over {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    {i : U ⟶ T} (hi : i ≫ hT = hU) (W : T.Opens) :
    (i ∣_ W) ≫ W.ι ≫ hT = (i ⁻¹ᵁ W).ι ≫ hU :=
  sorry

/-- The morphism in `Over S` associated to a scheme morphism over `S`. -/
def overHom {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    (i : U ⟶ T) (hi : i ≫ hT = hU) :
    Over.mk hU ⟶ Over.mk hT :=
  Over.homMk i hi

/-- `overHom i hi` has left component `i`. -/
theorem overHom_left {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    (i : U ⟶ T) (hi : i ≫ hT = hU) :
    (overHom i hi).left = i :=
  sorry

/-- The morphism in `Over S` induced by an open immersion of the source of
`hT`. -/
def openOverHom {S T : Scheme.{u}} (hT : T ⟶ S) (W : T.Opens) :
    Over.mk (W.ι ≫ hT) ⟶ Over.mk hT :=
  Over.homMk W.ι rfl

/-- `openOverHom hT W` has left component `W.ι`. -/
theorem openOverHom_left {S T : Scheme.{u}} (hT : T ⟶ S) (W : T.Opens) :
    (openOverHom hT W).left = W.ι :=
  sorry

/-- The morphism in `Over S` induced by restricting `i` to an open of the
target. -/
def restrictOpenOverHom {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    {i : U ⟶ T} (hi : i ≫ hT = hU) (W : T.Opens) :
    Over.mk ((i ⁻¹ᵁ W).ι ≫ hU) ⟶ Over.mk (W.ι ≫ hT) :=
  Over.homMk (i ∣_ W) (restrictOpen_over hi W)

/-- `restrictOpenOverHom hi W` has left component `i ∣_ W`. -/
theorem restrictOpenOverHom_left {S U T : Scheme.{u}} {hU : U ⟶ S} {hT : T ⟶ S}
    {i : U ⟶ T} (hi : i ≫ hT = hU) (W : T.Opens) :
    (restrictOpenOverHom hi W).left = i ∣_ W :=
  sorry

/-- Lemma 98.19.1: if `S` is locally Noetherian, `X` is a category fibred in
groupoids over `(Sch/S)_fppf` having (RS*), `x` lies over an affine finite-type
`U ⟶ S`, and `u` is a finite type point of `U` at which `x` is not versal, then
there exists a morphism `x ⟶ y` of `X` lying over a first-order thickening
`U ⟶ T` whose kernel sheaf is the skyscraper `κ(u)`, such that no open
neighbourhood `W ⊆ T` of `u` admits a map `y|_W ⟶ x` whose composite with the
restriction of `x ⟶ y` is the canonical `x|_{U ∩ W} ⟶ x`. -/
@[stacks 0G2J]
theorem exists_firstOrderThickening_of_not_isVersalAt
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] {U : Scheme.{u}} [IsAffine U]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u : U) [IsFiniteTypePoint u]
    (h : ¬ IsVersalAt hU x hx u) :
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
                      ⟨x, hx⟩ :=
  sorry

end AlgebraicGeometry.GroupoidsOver

