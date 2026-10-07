module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ringed sites

This module defines ringed sites and their morphisms independently of any particular
geometric category. Module-valued constructions over a ringed site belong in the
corresponding `Algebra.Category.ModuleCat.Sheaf` modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w uX vX uY vY uZ vZ

/-- A ringed site is a site equipped with a sheaf of rings. -/
@[stacks 03AD "(1)"]
structure RingedSite where
  carrier : Type u
  [str : Category.{v} carrier]
  siteTopology : GrothendieckTopology carrier
  structureSheaf : Sheaf siteTopology RingCat.{w}

/-- A ringed site coerces to its underlying category of objects. -/
instance : CoeSort RingedSite (Type u) where
  coe X := X.carrier

attribute [instance] RingedSite.str

namespace RingedSite

/-- A site with a ring-valued sheaf, viewed as a ringed site. -/
@[stacks 03AD "ring-sheaf presentation"]
abbrev ofRingSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J RingCat.{w}) :
    RingedSite.{u, v, w} where
  carrier := C
  siteTopology := J
  structureSheaf := 𝒪

/-- A site with a sheaf of commutative rings, viewed as a ringed site through the canonical
forgetful functor `CommRingCat ⥤ RingCat`. -/
@[stacks 03AD "commutative-ring-sheaf presentation"]
abbrev ofCommRingSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (𝒪 : Sheaf J CommRingCat.{w}) :
  RingedSite.{u, v, w} :=
  ofRingSheaf J
    (CategoryTheory.Sheaf.ringSheafOfComm 𝒪)

/-- A site with a sheaf of commutative `R`-algebras, viewed as a ringed site through its
underlying ring sheaf.  The input algebra sheaf remains the owner of the coefficient action;
this projection alone does not equip module sheaves or derived Hom with an `R`-linear structure. -/
@[stacks 0CS6 "underlying ringed site of a commutative algebra sheaf"]
abbrev ofCommAlgSheaf
    {R : Type uZ} [CommRing R]
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (𝒪 : Sheaf J (CommAlgCat.{w} R)) : RingedSite.{u, v, w} :=
  ofRingSheaf J (CategoryTheory.Sheaf.CommAlg.ring 𝒪)

/-- The max-universe underlying ringed site of a commutative `R`-algebra sheaf.  Limit
preservation supplies both sheaf-composition instances, so the coefficient ring, site, and
algebra sheaf are the only mathematical inputs. -/
@[stacks 0CS6 "max-universe underlying ringed site of an algebra sheaf"]
abbrev ofCommAlgSheafMax
    {R : Type uZ} [CommRing R]
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J (CommAlgCat.{max u v} R)) :
    RingedSite.{u, v, max u v} :=
  ofCommAlgSheaf J 𝒪

/-- The canonical max-universe ringed site attached to a commutative-ring sheaf.  At this
universe the forgetful functor preserves the multicospan limits defining the sheaf condition,
so downstream presentation APIs need no extra composition parameter. -/
@[stacks 03AD "canonical max-universe commutative presentation"]
abbrev ofCommSheafMax
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    RingedSite.{u, v, max u v} :=
  @ofCommRingSheaf C _ J
    (hasSheafCompose_of_preservesMulticospan J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})) 𝒪

-- The remaining `sorryAx` in the max presentation is confined to the Prop-valued
-- sheaf-composition instances supplied by `CommAlgCat.Limits`.

/-- A morphism of ringed sites consists of a morphism of sites and the adjoint
structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X`. -/
@[stacks 03AD "(2)"]
structure Hom
    (X : RingedSite.{uX, vX, w}) (Y : RingedSite.{uY, vY, w}) where
  base : Y ⥤ X
  [isMorphismOfSites : IsMorphismOfSites Y.siteTopology X.siteTopology base]
  structureSheafMap :
    Y.structureSheaf ⟶
      (base.sheafPushforwardContinuous RingCat.{w}
        Y.siteTopology X.siteTopology).obj X.structureSheaf

attribute [instance] Hom.isMorphismOfSites

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}

/-- The base functor of a morphism of ringed sites is continuous for the underlying site
topologies. -/
instance Hom.base_isContinuous (f : Hom X Y) :
    f.base.IsContinuous Y.siteTopology X.siteTopology :=
  f.isMorphismOfSites.toIsContinuous

/-- The base functor of a morphism of ringed sites is representably flat.  This direct projection
instance remains visible when the source and target ringed sites are given through reducible
presentation abbreviations. -/
@[stacks 03AD "representably flat base functor"]
instance Hom.base_representablyFlat (f : Hom X Y) :
    RepresentablyFlat f.base := sorry

/-- The representable-flatness projection remains available to typeclass search when both ringed
sites are presented by commutative-ring sheaves.  This specialized entry compensates for the
reducible `ofCommRingSheaf` presentation without adding a separate geometric hypothesis. -/
@[stacks 03AD "commutative presentation representably flat base"]
instance Hom.commRingBase_representablyFlat
    {CX : Type uX} [Category.{vX} CX] {CY : Type uY} [Category.{vY} CY]
    {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
    [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
    (f : Hom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY)) :
    RepresentablyFlat f.base := sorry

/-- The displayed composite of the base functors of two composable ringed-site morphisms is
continuous. This instance supports APIs whose type is indexed by `g.base ⋙ f.base` rather than
by the definitionally equal base functor of `f ≫ g`. -/
instance Hom.baseComp_isContinuous (f : Hom X Y) (g : Hom Y Z) :
    (g.base ⋙ f.base).IsContinuous Z.siteTopology X.siteTopology :=
  Functor.isContinuous_comp g.base f.base
    Z.siteTopology Y.siteTopology X.siteTopology

/-- The identity morphism of a ringed site. -/
noncomputable def Hom.id (X : RingedSite.{uX, vX, w}) : Hom X X where
  base := 𝟭 X
  isMorphismOfSites := by infer_instance
  structureSheafMap := 𝟙 X.structureSheaf

/-- Composition of morphisms of ringed sites. The underlying site morphism is the composite of
the underlying morphisms of sites, and the structure-sheaf map is composed in adjoint
pushforward form. -/
noncomputable def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := g.base ⋙ f.base
  isMorphismOfSites :=
    IsMorphismOfSites.comp
      Y.siteTopology g.base f.base
  structureSheafMap :=
    g.structureSheafMap ≫
      (g.base.sheafPushforwardContinuous RingCat.{w}
        Z.siteTopology Y.siteTopology).map f.structureSheafMap

/-- Ringed sites and their morphisms form a category. -/
@[stacks 03AD "(3)"]
instance : Category.{max u v w} (RingedSite.{u, v, w}) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := by
    rintro _ _ ⟨_, _, _⟩
    rfl
  comp_id := by
    rintro _ _ ⟨_, _, _⟩
    rfl
  assoc := by
    rintro _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩
    rfl

end RingedSite
