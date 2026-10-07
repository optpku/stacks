module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Torsor.Basic

/-!
# Restriction of fppf sheaves of groups and torsors

Inverse image of sheaves of types and groups along morphisms in `(Sch/S)_fppf`,
together with the inverse image of a torsor under a sheaf of groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsors

variable {S : Scheme.{u}}

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Restriction of an fppf sheaf of groups from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrictGrp (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of groups along a morphism in `Over S`. -/
def inverseImageGrp {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map f.left).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Restricting from `S` to `U'` and then pulling back along `f : U ⟶ U'` is
restriction to `U`. -/
def restrictIso {U U' : Over S} (f : U ⟶ U') :
    restrict U' ⋙ inverseImage f ≅ restrict U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    (Type u) (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

/-- Restricting a sheaf of groups from `S` to `U'` and then pulling back along
`f : U ⟶ U'` is restriction to `U`. -/
def restrictGrpIso {U U' : Over S} (f : U ⟶ U') :
    restrictGrp U' ⋙ inverseImageGrp f ≅ restrictGrp U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    GrpCat.{u} (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

/-- Group sections of `𝒢|_U` over `V` identify with group sections of the inverse
image of `𝒢|_U'`. -/
def restrictGrpIso_app {U U' : Over S} (f : U ⟶ U')
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) (V : Over U.left) :
    ((inverseImageGrp f).obj ((restrictGrp U').obj 𝒢)).obj.obj (op V) ≅
      ((restrictGrp U).obj 𝒢).obj.obj (op V) :=
  ((sheafToPresheaf (Scheme.fppfTopology.over U.left) GrpCat.{u}).mapIso
      ((restrictGrpIso f).app 𝒢)).app (op V)

/-- The transported action of a section of `𝒢|_U` on a section of `f⁻¹ P`. -/
def inverseImageTorsor_smul {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : ((inverseImage f).obj P.carrier).obj.obj (op V)) :
    ((inverseImage f).obj P.carrier).obj.obj (op V) :=
  (P.mulAction ((Over.map f.left).obj V)).smul
    ((Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V)).symm γ) x

/-- Inverse image of a `𝒢|_U'`-torsor along `f : U ⟶ U'`, as a `𝒢|_U`-torsor. -/
def inverseImageTorsor {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢)) :
    Sheaf.Torsor ((restrictGrp U).obj 𝒢) where
  carrier := (inverseImage f).obj P.carrier
  mulAction V :=
    { smul := inverseImageTorsor_smul f P V
      one_smul := sorry
      mul_smul := sorry }
  act_naturality := sorry
  isPretransitive := sorry
  isCancelSMul := sorry
  locallyNonempty := sorry

/-- The carrier of `inverseImageTorsor f P` is the inverse image of the carrier of `P`. -/
theorem inverseImageTorsor_carrier {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢)) :
    (inverseImageTorsor f P).carrier = (inverseImage f).obj P.carrier := sorry

/-- Isomorphisms in the explicit category of torsors under a sheaf of groups. -/
def TorsorIso {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {G : Sheaf J GrpCat.{u}} (P Q : Sheaf.Torsor G) :=
  @CategoryTheory.Iso (Sheaf.Torsor G) (@Sheaf.Torsor.category C _ J G) P Q

/-- Package a pair of inverse equivariant morphisms as a torsor isomorphism. -/
def TorsorIso.mk {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {G : Sheaf J GrpCat.{u}} {P Q : Sheaf.Torsor G}
    (hom : Sheaf.Torsor.Hom P Q) (inv : Sheaf.Torsor.Hom Q P) : TorsorIso P Q :=
  @Iso.mk (Sheaf.Torsor G) (@Sheaf.Torsor.category C _ J G) P Q hom inv sorry sorry

/-- Composition of explicit torsor isomorphisms. -/
def TorsorIso.trans {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {G : Sheaf J GrpCat.{u}} {P Q R : Sheaf.Torsor G}
    (α : TorsorIso P Q) (β : TorsorIso Q R) : TorsorIso P R :=
  @Iso.trans (Sheaf.Torsor G) (@Sheaf.Torsor.category C _ J G) P Q R α β

/-- The forward equivariant morphism of an explicit torsor isomorphism. -/
def TorsorIso.hom {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {G : Sheaf J GrpCat.{u}} {P Q : Sheaf.Torsor G} (α : TorsorIso P Q) :
    Sheaf.Torsor.Hom P Q :=
  @Iso.hom (Sheaf.Torsor G) (@Sheaf.Torsor.category C _ J G) P Q α

/-- The inverse equivariant morphism of an explicit torsor isomorphism. -/
def TorsorIso.inv {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {G : Sheaf J GrpCat.{u}} {P Q : Sheaf.Torsor G} (α : TorsorIso P Q) :
    Sheaf.Torsor.Hom Q P :=
  @Iso.inv (Sheaf.Torsor G) (@Sheaf.Torsor.category C _ J G) P Q α

/-- The identity comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorId_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor (𝟙 U) P).carrier.obj.obj (op V)) :
    ((inverseImageId U).hom.app P.carrier).hom.app (op V)
        (((inverseImageTorsor (𝟙 U) P).mulAction V).smul γ x) =
      (P.mulAction V).smul γ
        (((inverseImageId U).hom.app P.carrier).hom.app (op V) x) := sorry

/-- The inverse identity comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorId_inv_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V)) (x : P.carrier.obj.obj (op V)) :
    ((inverseImageId U).inv.app P.carrier).hom.app (op V)
        ((P.mulAction V).smul γ x) =
      ((inverseImageTorsor (𝟙 U) P).mulAction V).smul γ
        (((inverseImageId U).inv.app P.carrier).hom.app (op V) x) := sorry

/-- Inverse image of a torsor along an identity morphism is isomorphic to the
original torsor. -/
def inverseImageTorsorId {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U : Over S} (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) :
    TorsorIso (inverseImageTorsor (𝟙 U) P) P :=
  TorsorIso.mk
    { hom := (inverseImageId U).hom.app P.carrier
      comm := inverseImageTorsorId_hom_comm P }
    { hom := (inverseImageId U).inv.app P.carrier
      comm := inverseImageTorsorId_inv_comm P }

/-- The composite comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorComp_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' U'' : Over S}
    (f : U ⟶ U') (g : U' ⟶ U'') (P : Sheaf.Torsor ((restrictGrp U'').obj 𝒢))
    (V : Over U.left) (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor (f ≫ g) P).carrier.obj.obj (op V)) :
    ((inverseImageComp f g).inv.app P.carrier).hom.app (op V)
        (((inverseImageTorsor (f ≫ g) P).mulAction V).smul γ x) =
      ((inverseImageTorsor f (inverseImageTorsor g P)).mulAction V).smul γ
        (((inverseImageComp f g).inv.app P.carrier).hom.app (op V) x) := sorry

/-- The inverse composite comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorComp_inv_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' U'' : Over S}
    (f : U ⟶ U') (g : U' ⟶ U'') (P : Sheaf.Torsor ((restrictGrp U'').obj 𝒢))
    (V : Over U.left) (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor f (inverseImageTorsor g P)).carrier.obj.obj (op V)) :
    ((inverseImageComp f g).hom.app P.carrier).hom.app (op V)
        (((inverseImageTorsor f (inverseImageTorsor g P)).mulAction V).smul γ x) =
      ((inverseImageTorsor (f ≫ g) P).mulAction V).smul γ
        (((inverseImageComp f g).hom.app P.carrier).hom.app (op V) x) := sorry

/-- Inverse image of torsors is contravariant for composition of scheme maps. -/
def inverseImageTorsorComp {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'')
    (P : Sheaf.Torsor ((restrictGrp U'').obj 𝒢)) :
    TorsorIso (inverseImageTorsor (f ≫ g) P)
      (inverseImageTorsor f (inverseImageTorsor g P)) :=
  TorsorIso.mk
    { hom := (inverseImageComp f g).inv.app P.carrier
      comm := inverseImageTorsorComp_hom_comm f g P }
    { hom := (inverseImageComp f g).hom.app P.carrier
      comm := inverseImageTorsorComp_inv_comm f g P }

/-- Inverse image of an equivariant morphism of torsors is equivariant. -/
theorem inverseImageTorsorMap_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' : Over S}
    (f : U ⟶ U') {P Q : Sheaf.Torsor ((restrictGrp U').obj 𝒢)}
    (α : TorsorIso P Q) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor f P).carrier.obj.obj (op V)) :
    ((inverseImage f).map (TorsorIso.hom α).hom).hom.app (op V)
        (((inverseImageTorsor f P).mulAction V).smul γ x) =
      ((inverseImageTorsor f Q).mulAction V).smul γ
        (((inverseImage f).map (TorsorIso.hom α).hom).hom.app (op V) x) := sorry

/-- Inverse image of the inverse of an equivariant morphism of torsors is
equivariant. -/
theorem inverseImageTorsorMap_inv_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' : Over S}
    (f : U ⟶ U') {P Q : Sheaf.Torsor ((restrictGrp U').obj 𝒢)}
    (α : TorsorIso P Q) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor f Q).carrier.obj.obj (op V)) :
    ((inverseImage f).map (TorsorIso.inv α).hom).hom.app (op V)
        (((inverseImageTorsor f Q).mulAction V).smul γ x) =
      ((inverseImageTorsor f P).mulAction V).smul γ
        (((inverseImage f).map (TorsorIso.inv α).hom).hom.app (op V) x) := sorry

/-- Inverse image of torsors is functorial in isomorphisms of torsors. -/
def inverseImageTorsorMap {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') {P Q : Sheaf.Torsor ((restrictGrp U').obj 𝒢)}
    (α : TorsorIso P Q) :
    TorsorIso (inverseImageTorsor f P) (inverseImageTorsor f Q) :=
  TorsorIso.mk
    { hom := (inverseImage f).map (TorsorIso.hom α).hom
      comm := inverseImageTorsorMap_hom_comm f α }
    { hom := (inverseImage f).map (TorsorIso.inv α).hom
      comm := inverseImageTorsorMap_inv_comm f α }

/-- Restriction of a sheaf of groups to `U` is `𝒢|_U`. -/
theorem restrictGrp_obj (U : Over S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    (restrictGrp U).obj 𝒢 =
      ((Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
        (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)).obj 𝒢 :=
  sorry

end AlgebraicGeometry.SheafTorsors
