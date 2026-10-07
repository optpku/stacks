module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Transitivity for conormal sheaves of scheme immersions

For composable immersions `Z ⟶ Y ⟶ X`, the canonical conormal comparison maps form the
right-exact transitivity sequence

  i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0.

The comparison maps and their short complex are explicit data; exactness and epimorphy are
recorded separately.
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

/-- The canonical map from the pullback of `C_{Y/X}` to `C_{Z/X}` for composable scheme
morphisms `Z ⟶ Y ⟶ X`. -/
noncomputable def baseChange (i : Z ⟶ Y) (j : Y ⟶ X) :
    (Scheme.Modules.pullback i).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf (i ≫ j) :=
  Conormal.map (f := i) (i := i ≫ j) (i' := j) (g := 𝟙 X) ⟨by simp⟩

/-- The canonical map from `C_{Z/X}` to `C_{Z/Y}` for composable scheme morphisms
`Z ⟶ Y ⟶ X`. -/
noncomputable def projection (i : Z ⟶ Y) (j : Y ⟶ X) :
    Scheme.Hom.conormalSheaf (i ≫ j) ⟶ Scheme.Hom.conormalSheaf i :=
  (Scheme.Modules.pullbackId Z).inv.app (Scheme.Hom.conormalSheaf (i ≫ j)) ≫
    Conormal.map (f := 𝟙 Z) (i := i) (i' := i ≫ j) (g := j) ⟨by simp⟩

/-- The canonical conormal transitivity maps have zero composite. -/
theorem baseChange_comp_projection (i : Z ⟶ Y) (j : Y ⟶ X) :
    baseChange i j ≫ projection i j = 0 := sorry

/-- The canonical conormal transitivity short complex for composable scheme morphisms. -/
noncomputable def complex (i : Z ⟶ Y) (j : Y ⟶ X) : ShortComplex Z.Modules :=
  ShortComplex.mk (baseChange i j) (projection i j) (baseChange_comp_projection i j)

/-- The canonical conormal transitivity short complex of two scheme immersions is exact. -/
theorem exact (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact := sorry

/-- The projection in the conormal transitivity sequence of two scheme immersions is an
epimorphism. -/
instance projection_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    Epi (projection i j) := sorry

/-- For two composable scheme immersions, the canonical conormal transitivity complex is exact
and its projection is an epimorphism. -/
theorem exact_and_epi (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (complex i j).Exact ∧ Epi (projection i j) :=
  ⟨exact i j, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity
