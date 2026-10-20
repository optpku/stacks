module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Local splittings of conormal transitivity sequences

For composable scheme immersions, this file records when the canonical conormal transitivity
complex is short exact and splits after restriction to a source-open neighborhood of every
point.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})]

/-- The canonical conormal transitivity complex of two scheme immersions is short exact and
splits after restriction to a source-open neighborhood of every point. -/
def IsShortExactLocallySplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] : Prop :=
  (complex i j).ShortExact ∧
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      Nonempty (((complex i j).map (Scheme.Modules.pullback U.ι)).Splitting)

/-- Short exactness and source-open local splittings characterize a locally split conormal
transitivity complex. -/
theorem isShortExactLocallySplit_iff
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    IsShortExactLocallySplit i j ↔
      (complex i j).ShortExact ∧
        ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
          Nonempty (((complex i j).map (Scheme.Modules.pullback U.ι)).Splitting) :=
  Iff.rfl

/-- The canonical conormal transitivity complex of two scheme immersions splits after
restriction to a source-open neighborhood of a specified point. -/
def IsSplitExactNear
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) : Prop :=
  ∃ U : Z.Opens, z ∈ U ∧
    Nonempty (((complex i j).map (Scheme.Modules.pullback U.ι)).Splitting)

/-- A splitting of the restricted canonical conormal transitivity complex on some source-open
neighborhood characterizes split exactness near a specified point. -/
theorem isSplitExactNear_iff
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) :
    IsSplitExactNear i j z ↔
      ∃ U : Z.Opens, z ∈ U ∧
        Nonempty (((complex i j).map (Scheme.Modules.pullback U.ι)).Splitting) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity
