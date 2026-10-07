module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity

/-!
# Transitivity between conormal sheaves and relative differentials

For composable scheme morphisms `Z ⟶ X ⟶ Y`, the canonical conormal projection and the
conormal-to-differentials map form a short complex. When `Z ⟶ X` and `Z ⟶ Y` are immersions,
this complex is exact and its right arrow is an epimorphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity

variable {Z X Y : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- The canonical projection from `C_{Z/Y}` to `C_{Z/X}` followed by the canonical map from
`C_{Z/X}` to the pullback of `Ω_{X/Y}` is zero. -/
theorem projection_comp_map (i : Z ⟶ X) (f : X ⟶ Y) :
    Conormal.Transitivity.projection i f ≫ Conormal.Differentials.map i f = 0 := sorry

/-- The canonical short complex from `C_{Z/Y}` through `C_{Z/X}` to the pullback of
`Ω_{X/Y}`. -/
noncomputable def complex (i : Z ⟶ X) (f : X ⟶ Y) : ShortComplex Z.Modules :=
  ShortComplex.mk (Conormal.Transitivity.projection i f) (Conormal.Differentials.map i f)
    (projection_comp_map i f)

/-- If `Z ⟶ X` and `Z ⟶ Y` are immersions, the canonical conormal-differentials complex is
exact. -/
theorem exact (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] :
    (complex i f).Exact := sorry

/-- If `Z ⟶ X` and `Z ⟶ Y` are immersions, the canonical map from `C_{Z/X}` to the pullback
of `Ω_{X/Y}` is an epimorphism. -/
instance map_epi (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] :
    Epi (Conormal.Differentials.map i f) := sorry

/-- If `Z ⟶ X` and `Z ⟶ Y` are immersions, the canonical conormal-differentials complex is
exact and its right arrow is an epimorphism. -/
theorem exact_and_epi (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] :
    (complex i f).Exact ∧ Epi (Conormal.Differentials.map i f) :=
  ⟨exact i f, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity
