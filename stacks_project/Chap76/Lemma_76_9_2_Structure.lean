module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap66.Lemma_66_27_1_Hom

/-!
# Spaces-étale structure sheaves of thickenings

A thickening `i : X ⟶ X'` lets `𝒪_{X'}` be viewed as the inverse image sheaf
`i_{spaces,étale}⁻¹ 𝒪_{X'}` on `X_spaces,étale`. Morphisms of thickenings are
compared with this inverse-image form of `(f')^♯`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

variable {S : Scheme.{u}}

/-- Continuous type-valued pushforward along `spacesEtalePullback` of a composite
identifies with the composite of the pushforwards. -/
def spacesEtalePushforwardCompIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.sheafPushforwardContinuousComp' (spacesEtalePullbackComp f g).symm (Type u)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- `spacesEtalePushforwardCompIso` is `sheafPushforwardContinuousComp'` of
`spacesEtalePullbackComp`. -/
theorem spacesEtalePushforwardCompIso_eq {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtalePushforwardCompIso f g =
      Functor.sheafPushforwardContinuousComp' (spacesEtalePullbackComp f g).symm (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Inverse images of `spacesRingedToposHom` along a composite and along the corresponding
composite of topos morphisms. -/
def inverseImageCompIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesRingedToposHom (f ≫ g)).toTopos.inverseImage ≅
      (MorphismOfTopoiIn.comp (spacesRingedToposHom g).toTopos
        (spacesRingedToposHom f).toTopos).inverseImage :=
  Adjunction.leftAdjointUniq
    (spacesRingedToposHom (f ≫ g)).toTopos.adjunction
    (((spacesRingedToposHom g).toTopos.adjunction.comp
        (spacesRingedToposHom f).toTopos.adjunction).ofNatIsoRight
      (spacesEtalePushforwardCompIso f g))

/-- Ring-valued inverse image along a composite morphism of algebraic spaces identifies with
the composite of the ring-valued inverse images. -/
def ringInverseImageCompAssocIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesRingedToposHom (f ≫ g)).toTopos.ringInverseImage ≅
      (spacesRingedToposHom g).toTopos.ringInverseImage ⋙
        (spacesRingedToposHom f).toTopos.ringInverseImage :=
  MorphismOfTopoiIn.ringInverseImageNatIso
      (f := (spacesRingedToposHom (f ≫ g)).toTopos)
      (g := MorphismOfTopoiIn.comp
        (spacesRingedToposHom g).toTopos
        (spacesRingedToposHom f).toTopos)
      (inverseImageCompIso f g) ≪≫
    MorphismOfTopoiIn.ringInverseImageCompIso
      (spacesRingedToposHom g).toTopos
      (spacesRingedToposHom f).toTopos

/-- Equal morphisms of algebraic spaces induce equal ring-valued inverse-image functors. -/
def ringInverseImageCongr {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b) :
    (spacesRingedToposHom a).toTopos.ringInverseImage ≅
      (spacesRingedToposHom b).toTopos.ringInverseImage :=
  eqToIso (congrArg (fun t : X ⟶ Y ↦ (spacesRingedToposHom t).toTopos.ringInverseImage) h)

/-- The sheaf `i_{spaces,étale}⁻¹ 𝒪_{X'}` on `X_spaces,étale`. -/
def closedStructureSheaf {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  (spacesRingedToposHom i).toTopos.ringInverseImage.obj (spacesStructureSheaf X')

/-- `closedStructureSheaf i` is ring-valued inverse image of `spacesStructureSheaf X'`. -/
theorem closedStructureSheaf_eq {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    closedStructureSheaf i =
      (spacesRingedToposHom i).toTopos.ringInverseImage.obj (spacesStructureSheaf X') :=
  rfl

/-- The structure map `i^♯ : i_{spaces,étale}⁻¹ 𝒪_{X'} ⟶ 𝒪_X` on `X_spaces,étale`. -/
def closedStructureSheaf_structureMap {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    closedStructureSheaf i ⟶ spacesStructureSheaf X :=
  (spacesRingedToposHom i).structureMap

/-- `closedStructureSheaf_structureMap i` is the inverse-image structure map of
`spacesRingedToposHom i`. -/
theorem closedStructureSheaf_structureMap_eq {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    closedStructureSheaf_structureMap i = (spacesRingedToposHom i).structureMap :=
  rfl

/-- The sheaf `f_{spaces,étale}⁻¹ 𝒪_{Y'}` on `X_spaces,étale`, obtained by inverse image of
`closedStructureSheaf iY`. -/
def inverseImageClosedStructureSheaf {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (iY : Y ⟶ Y') :
    Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  (spacesRingedToposHom f).toTopos.ringInverseImage.obj (closedStructureSheaf iY)

/-- `inverseImageClosedStructureSheaf f iY` is ring-valued inverse image of
`closedStructureSheaf iY`. -/
theorem inverseImageClosedStructureSheaf_eq {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (iY : Y ⟶ Y') :
    inverseImageClosedStructureSheaf f iY =
      (spacesRingedToposHom f).toTopos.ringInverseImage.obj (closedStructureSheaf iY) :=
  rfl

/-- The inverse image `s^{-1} 𝒪_B` of the structure sheaf of `B` along a structure morphism
`s : X ⟶ B`, as a sheaf of rings on `X_spaces,étale`. -/
def inverseImageBaseSheaf {B X : AlgebraicSpace S} (s : X ⟶ B) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  (spacesRingedToposHom s).toTopos.ringInverseImage.obj (spacesStructureSheaf B)

/-- `inverseImageBaseSheaf s` is ring-valued inverse image of `spacesStructureSheaf B`. -/
theorem inverseImageBaseSheaf_eq {B X : AlgebraicSpace S} (s : X ⟶ B) :
    inverseImageBaseSheaf s =
      (spacesRingedToposHom s).toTopos.ringInverseImage.obj (spacesStructureSheaf B) :=
  rfl

/-- The `𝒪_B`-algebra structure map `sX^{-1} 𝒪_B ⟶ i^{-1} 𝒪_{X'}` of a thickening over `B`. -/
def closedAlgebraMap {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (hX : i ≫ sX' = sX) :
    inverseImageBaseSheaf sX ⟶ closedStructureSheaf i :=
  (ringInverseImageCongr hX.symm).hom.app (spacesStructureSheaf B) ≫
    (ringInverseImageCompAssocIso i sX').hom.app (spacesStructureSheaf B) ≫
    (spacesRingedToposHom i).toTopos.ringInverseImage.map
      (spacesRingedToposHom sX').structureMap

/-- `closedAlgebraMap` is the transport of `i^{-1}((sX')^♯)` along the composite identification
`sX^{-1} ≅ i^{-1} (sX')^{-1}`. -/
theorem closedAlgebraMap_eq {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (hX : i ≫ sX' = sX) :
    closedAlgebraMap i sX sX' hX =
      (ringInverseImageCongr hX.symm).hom.app (spacesStructureSheaf B) ≫
        (ringInverseImageCompAssocIso i sX').hom.app (spacesStructureSheaf B) ≫
        (spacesRingedToposHom i).toTopos.ringInverseImage.map
          (spacesRingedToposHom sX').structureMap :=
  sorry

/-- The `𝒪_B`-algebra structure map `sX^{-1} 𝒪_B ⟶ f^{-1} 𝒪_{Y'}` obtained by inverse image of
`closedAlgebraMap iY` along `f`. -/
def inverseImageClosedAlgebraMap {B X Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (f : X ⟶ Y) (iY : Y ⟶ Y') (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX) :
    inverseImageBaseSheaf sX ⟶ inverseImageClosedStructureSheaf f iY :=
  (ringInverseImageCongr hf.symm).hom.app (spacesStructureSheaf B) ≫
    (ringInverseImageCompAssocIso f sY).hom.app (spacesStructureSheaf B) ≫
    (spacesRingedToposHom f).toTopos.ringInverseImage.map
      (closedAlgebraMap iY sY sY' hY)

/-- `inverseImageClosedAlgebraMap` is the transport of `f^{-1}(closedAlgebraMap iY)` along
`sX^{-1} ≅ f^{-1} sY^{-1}`. -/
theorem inverseImageClosedAlgebraMap_eq {B X Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (f : X ⟶ Y) (iY : Y ⟶ Y') (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX) :
    inverseImageClosedAlgebraMap sX sY sY' f iY hY hf =
      (ringInverseImageCongr hf.symm).hom.app (spacesStructureSheaf B) ≫
        (ringInverseImageCompAssocIso f sY).hom.app (spacesStructureSheaf B) ≫
        (spacesRingedToposHom f).toTopos.ringInverseImage.map
          (closedAlgebraMap iY sY sY' hY) :=
  sorry

/-- The inverse-image form of `(f')^♯`, transported to a map
`f_{spaces,étale}⁻¹ 𝒪_{Y'} ⟶ 𝒪_{X'}` on `X_spaces,étale`. -/
def structureMap_transported {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h_comm : iX ≫ f' = f ≫ iY) :
    inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX :=
  (ringInverseImageCompAssocIso f iY).inv.app (spacesStructureSheaf Y') ≫
    (ringInverseImageCongr h_comm.symm).hom.app (spacesStructureSheaf Y') ≫
    (ringInverseImageCompAssocIso iX f').hom.app (spacesStructureSheaf Y') ≫
    (spacesRingedToposHom iX).toTopos.ringInverseImage.map
      (spacesRingedToposHom f').structureMap

/-- `structureMap_transported` is `iX^{-1}((f')^♯)` after identifying
`f^{-1} iY^{-1} ≅ (iX ≫ f')^{-1} ≅ iX^{-1} (f')^{-1}`. -/
theorem structureMap_transported_eq {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h_comm : iX ≫ f' = f ≫ iY) :
    structureMap_transported iX iY f f' h_comm =
      (ringInverseImageCompAssocIso f iY).inv.app (spacesStructureSheaf Y') ≫
        (ringInverseImageCongr h_comm.symm).hom.app (spacesStructureSheaf Y') ≫
        (ringInverseImageCompAssocIso iX f').hom.app (spacesStructureSheaf Y') ≫
        (spacesRingedToposHom iX).toTopos.ringInverseImage.map
          (spacesRingedToposHom f').structureMap :=
  sorry

/-- The source commutative square: `α` followed by `iX^♯` equals `f^{-1}(iY^♯)` followed by
`f^♯`. -/
def structureMap_commutes {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX) : Prop :=
  α ≫ closedStructureSheaf_structureMap iX =
    (spacesRingedToposHom f).toTopos.ringInverseImage.map
      (closedStructureSheaf_structureMap iY) ≫
    (spacesRingedToposHom f).structureMap

/-- `structureMap_commutes` is the equality of the two paths around the structure-sheaf
square. -/
theorem structureMap_commutes_iff {X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX) :
    structureMap_commutes iX iY f α ↔
      α ≫ closedStructureSheaf_structureMap iX =
        (spacesRingedToposHom f).toTopos.ringInverseImage.map
          (closedStructureSheaf_structureMap iY) ≫
        (spacesRingedToposHom f).structureMap :=
  sorry

/-- The map `α` is a morphism of `sX^{-1} 𝒪_B`-algebras. -/
def isAlgebraOverBase {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX) : Prop :=
  inverseImageClosedAlgebraMap sX sY sY' f iY hY hf ≫ α =
    closedAlgebraMap iX sX sX' hX

/-- `isAlgebraOverBase` is the triangle equality for the two maps from `sX^{-1} 𝒪_B`. -/
theorem isAlgebraOverBase_iff {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX) :
    isAlgebraOverBase sX sX' sY sY' iX iY f hX hY hf α ↔
      inverseImageClosedAlgebraMap sX sY sY' f iY hY hf ≫ α =
        closedAlgebraMap iX sX sX' hX :=
  sorry

/-- A morphism `f' : X' ⟶ Y'` of thickenings over `B` with inverse-image structure map `α`. -/
structure IsHom {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') : Prop where
  /-- The pair `(f, f')` is a morphism of thickenings. -/
  w : iX ≫ f' = f ≫ iY
  /-- The morphism `f'` lies over `B`. -/
  overBase : f' ≫ sY' = sX'
  /-- The inverse-image structure map of `f'` recovers `α`. -/
  structureMap_eq : structureMap_transported iX iY f f' w = α

/-- Assemble a morphism of thickenings over `B` from the commutative square, the map over
`B`, and the identification `α = (f')^♯`. -/
def IsHom.of {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') (h_comm : iX ≫ f' = f ≫ iY) (h_over : f' ≫ sY' = sX')
    (hα : structureMap_transported iX iY f f' h_comm = α) :
    IsHom sX' sY' iX iY f α f' where
  w := h_comm
  overBase := h_over
  structureMap_eq := hα

/-- Being a morphism of thickenings over `B` with structure map `α` unpacks as the
commutative square, the map over `B`, and `α = (f')^♯`. -/
theorem isHom_iff {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') :
    IsHom sX' sY' iX iY f α f' ↔
      ∃ h_comm : iX ≫ f' = f ≫ iY,
        f' ≫ sY' = sX' ∧ structureMap_transported iX iY f f' h_comm = α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening
