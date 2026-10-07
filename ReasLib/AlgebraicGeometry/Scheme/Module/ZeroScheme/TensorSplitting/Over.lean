module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Tensor-section splittings over a base scheme

This file equips the schemes in a tensor-section splitting with their natural
maps to a common base and records the geometric properties of those maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TensorSectionSplitting

variable {S : Scheme.{u}} (Y : Over S)
variable {L₁ L₂ : Y.left.Modules}
variable [Modules.Invertible L₁] [Modules.Invertible L₂]
variable {s : (L₁ ⊗ L₂).sections} (C : TensorSectionSplitting L₁ L₂ s)

/-- The total scheme of a tensor-section splitting, regarded over `S`. -/
noncomputable def totalOver : Over S :=
  Over.mk (C.p ≫ Y.hom)

/-- The structure morphism of `totalOver` is the splitting projection followed by
the structure morphism of `Y`. -/
theorem totalOver_hom :
    (totalOver Y C).hom = C.p ≫ Y.hom := sorry

/-- The base zero scheme of a tensor-section splitting, regarded over `S`. -/
noncomputable def baseZeroOver : Over S :=
  Over.mk (C.baseι ≫ Y.hom)

/-- The structure morphism of `baseZeroOver` is the zero-scheme inclusion followed by
the structure morphism of `Y`. -/
theorem baseZeroOver_hom :
    (baseZeroOver Y C).hom = C.baseι ≫ Y.hom := sorry

/-- The first factor zero scheme of a tensor-section splitting, regarded over `S`. -/
noncomputable def zero₁Over : Over S :=
  Over.mk (C.ι₁ ≫ (C.p ≫ Y.hom))

/-- The structure morphism of `zero₁Over` is the first zero-scheme inclusion followed
by the splitting projection and the structure morphism of `Y`. -/
theorem zero₁Over_hom :
    (zero₁Over Y C).hom = C.ι₁ ≫ (C.p ≫ Y.hom) := sorry

/-- The first chosen relative-spectrum line model, regarded over `S`. -/
noncomputable def lineModel₁Over : Over S :=
  Over.mk (C.lineModel₁.π ≫ (C.baseι ≫ Y.hom))

/-- The structure morphism of `lineModel₁Over` is its line-bundle projection followed
by the base-zero inclusion and the structure morphism of `Y`. -/
theorem lineModel₁Over_hom :
    (lineModel₁Over Y C).hom = C.lineModel₁.π ≫ (C.baseι ≫ Y.hom) := sorry

/-- The underlying first line-model isomorphism commutes with the structure maps to `S`. -/
theorem lineIso₁Over_comm :
    ((Over.forget C.baseZero).mapIso C.lineIso₁).hom ≫
        (C.lineModel₁.π ≫ (C.baseι ≫ Y.hom)) =
      C.ι₁ ≫ (C.p ≫ Y.hom) := sorry

/-- The first zero scheme and its chosen line model are isomorphic over `S`. -/
noncomputable def lineIso₁Over : zero₁Over Y C ≅ lineModel₁Over Y C :=
  Over.isoMk ((Over.forget C.baseZero).mapIso C.lineIso₁)
    (lineIso₁Over_comm Y C)

/-- The underlying map of `lineIso₁Over` is the map underlying the splitting's chosen
line-model isomorphism. -/
theorem lineIso₁Over_hom_left :
    (lineIso₁Over Y C).hom.left = C.lineIso₁.hom.left := sorry

/-- The total scheme of a splitting remains locally of finite type over `S`. -/
theorem totalOver_locallyOfFiniteType [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (totalOver Y C).hom := sorry

/-- The base zero scheme remains locally of finite type over `S`. -/
theorem baseZeroOver_locallyOfFiniteType [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (baseZeroOver Y C).hom := sorry

/-- The first factor zero scheme remains locally of finite type over `S`. -/
theorem zero₁Over_locallyOfFiniteType [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (zero₁Over Y C).hom := sorry

/-- The first chosen line model remains locally of finite type over `S`. -/
theorem lineModel₁Over_locallyOfFiniteType [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (lineModel₁Over Y C).hom := sorry

/-- The first line-model projection, viewed over `S`, is flat. -/
theorem lineModel₁Projection_flat :
    Flat (Over.homMk C.lineModel₁.π : lineModel₁Over Y C ⟶ baseZeroOver Y C).left := sorry

/-- The first line-model projection, viewed over `S`, has relative dimension one. -/
theorem lineModel₁Projection_relativeDimension :
    Hom.RelativeDimension
      (Over.homMk C.lineModel₁.π : lineModel₁Over Y C ⟶ baseZeroOver Y C).left 1 := sorry

/-- The inverse of the first line-model isomorphism is proper on underlying schemes. -/
theorem lineIso₁Over_inv_isProper :
    IsProper (lineIso₁Over Y C).inv.left := sorry

end AlgebraicGeometry.Scheme.TensorSectionSplitting
