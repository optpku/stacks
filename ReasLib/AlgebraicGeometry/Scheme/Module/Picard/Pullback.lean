module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Pullback on Picard groups of schemes

This file specializes Picard functoriality to morphisms of schemes.  Its public API is expressed
only in terms of scheme modules and `Scheme.PicardGroup`; the skeleton construction and its
representatives remain owned by the generic commutative-ringed-site Picard group.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

/-- The Picard class represented by the pullback of an invertible scheme module. -/
noncomputable abbrev picardPullbackClass
    (f : X ⟶ Y) (L : Y.Modules) [MonoidalCategory.isInvertibleObject L] :
    X.PicardGroup :=
  @Scheme.Modules.picardClass X ((Scheme.Modules.pullback f).obj L)
    (@MonoidalCategory.isInvertibleObject.map
      Y.Modules _ _ X.Modules _ _ (Scheme.Modules.pullback f)
      (Scheme.Modules.pullbackMonoidal f) L _)

/-- The additive homomorphism on Picard groups induced by pullback along a scheme morphism. -/
@[stacks 040C "pullback on Picard groups of schemes"]
noncomputable def picardPullback (f : X ⟶ Y) :
    Y.PicardGroup →+ X.PicardGroup :=
  @MonoidalCategory.PicardGroup.map
    Y.Modules _ _ X.Modules _ _ (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackMonoidal f)

/-- Pullback sends the class of an invertible module to the class of its pullback. -/
@[simp]
theorem picardPullback_apply_class
    (f : X ⟶ Y) (L : Y.Modules) [MonoidalCategory.isInvertibleObject L] :
    picardPullback f (Scheme.Modules.picardClass L) =
      picardPullbackClass f L := sorry

/-- The representative of a pulled-back Picard class is canonically the pullback of its
representative. -/
@[stacks 040C "representative of a pulled-back scheme Picard class"]
noncomputable abbrev picardPullbackReprIso (f : X ⟶ Y) (x : Y.PicardGroup) :
    Scheme.PicardGroup.repr (picardPullback f x) ≅
      (Scheme.Modules.pullback f).obj (Scheme.PicardGroup.repr x) :=
  @MonoidalCategory.PicardGroup.reprMapIso
    Y.Modules _ _ X.Modules _ _ (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackMonoidal f) x

/-- Pullback along the identity morphism acts as the identity on the Picard group. -/
@[simp]
theorem picardPullback_id :
    picardPullback (𝟙 X) = AddMonoidHom.id X.PicardGroup := sorry

/-- Pullback along the identity morphism fixes every Picard class. -/
@[simp]
theorem picardPullback_id_apply (x : X.PicardGroup) :
    picardPullback (𝟙 X) x = x := sorry

/-- Pullback on Picard groups is contravariantly compatible with composition. -/
@[simp]
theorem picardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPullback (f ≫ g) = (picardPullback f).comp (picardPullback g) := sorry

/-- Pullback of a Picard class along a composite is the composite of the pullback maps. -/
@[simp]
theorem picardPullback_comp_apply
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Z.PicardGroup) :
    picardPullback (f ≫ g) x =
      picardPullback f (picardPullback g x) := sorry

end AlgebraicGeometry.Scheme.Hom
