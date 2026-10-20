module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Ringed.Map
public import Mathlib.CategoryTheory.Category.Cat
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

universe u v w uX vX uY vY uZ vZ t

namespace RingedSite

/-- The category of sites equipped with ring sheaves and explicit ringed-site maps. -/
abbrev category : Cat.{max u v w, max (u + 1) (v + 1) (w + 1)} :=
  ⟨(Σ C : Cat.{v, u}, Σ J : GrothendieckTopology C, Sheaf J RingCat.{w}), {
    Hom := fun X Y ↦ CategoryTheory.RingedSiteMap X.2.1 X.2.2 Y.2.1 Y.2.2
    id := fun X ↦ CategoryTheory.RingedSiteMap.id X.2.1 X.2.2
    comp := fun f g ↦ CategoryTheory.RingedSiteMap.comp f g
    id_comp := by rintro _ _ ⟨_, _, _⟩; rfl
    comp_id := by rintro _ _ ⟨_, _, _⟩; rfl
    assoc := by rintro _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩; rfl
  }⟩

end RingedSite

/-- A ringed site consists of a category, a Grothendieck topology, and a sheaf of rings. -/
@[stacks 03AD "(1)"]
abbrev RingedSite : Type (max (u + 1) (v + 1) (w + 1)) :=
  RingedSite.category.{u, v, w}

namespace RingedSite

/-- The category of ringed sites with explicit ringed-site maps as morphisms. -/
instance instCategory : Category.{max u v w} RingedSite.{u, v, w} :=
  Cat.str RingedSite.category

/-- The underlying category of a ringed site. -/
abbrev carrier (X : RingedSite.{u, v, w}) : Cat.{v, u} := X.1

/-- A ringed site coerces to the object type of its underlying category. -/
instance carrierCoeSort : CoeSort RingedSite.{u, v, w} (Type u) := ⟨fun X ↦ X.carrier⟩

/-- The Grothendieck topology of a ringed site. -/
abbrev siteTopology (X : RingedSite.{u, v, w}) : GrothendieckTopology X.carrier := X.2.1

/-- The ring-valued structure sheaf of a ringed site. -/
abbrev structureSheaf (X : RingedSite.{u, v, w}) : Sheaf X.siteTopology RingCat.{w} :=
  X.2.2

/-- A site with a ring-valued sheaf, viewed as a ringed site. -/
@[stacks 03AD "ring-sheaf presentation"]
abbrev ofRingSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J RingCat.{w}) :
    RingedSite.{u, v, w} :=
  ⟨⟨C, inferInstance⟩, J, 𝒪⟩

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

/-- A morphism of ringed sites is an explicit map of the underlying ringed-site data. -/
abbrev Hom
    (X : RingedSite.{uX, vX, w}) (Y : RingedSite.{uY, vY, w}) :=
  CategoryTheory.RingedSiteMap X.siteTopology X.structureSheaf
    Y.siteTopology Y.structureSheaf

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}

namespace Hom

/-- The base functor of a ringed-site map is continuous for the underlying site topologies. -/
theorem base_isContinuous (f : Hom X Y) :
    f.base.IsContinuous Y.siteTopology X.siteTopology :=
  f.isMorphismOfSites.toIsContinuous

/-- The base functor of a ringed-site map is representably flat. -/
theorem base_representablyFlat (f : Hom X Y) :
    RepresentablyFlat f.base :=
  f.isMorphismOfSites.toRepresentablyFlat

/-- The representable-flatness projection for a commutative-ring presentation. -/
theorem commRingBase_representablyFlat
    {CX : Type uX} [Category.{vX} CX] {CY : Type uY} [Category.{vY} CY]
    {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
    [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
    (f : Hom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY)) :
    RepresentablyFlat f.base :=
  f.isMorphismOfSites.toRepresentablyFlat

/-- The displayed composite of base functors is continuous. -/
theorem baseComp_isContinuous (f : Hom X Y) (g : Hom Y Z) :
    (g.base ⋙ f.base).IsContinuous Z.siteTopology X.siteTopology :=
  @Functor.isContinuous_comp _ _ _ _ _ _ g.base f.base
    Z.siteTopology Y.siteTopology X.siteTopology
    g.isMorphismOfSites.toIsContinuous f.isMorphismOfSites.toIsContinuous

/-- The continuous sheaf pushforward associated to an explicit ringed-site map. -/
noncomputable abbrev sheafPushforwardContinuous
    {A : Type u} [Category.{v} A] (f : Hom X Y) :
    Sheaf X.siteTopology A ⥤ Sheaf Y.siteTopology A :=
  @Functor.sheafPushforwardContinuous _ _ _ _ f.base A _
    Y.siteTopology X.siteTopology f.isMorphismOfSites.toIsContinuous

/-- The sheaf pullback left adjoint to continuous pushforward along a ringed-site map. -/
noncomputable abbrev sheafPullback
    {A : Type u} [Category.{v} A] (f : Hom X Y)
    [(f.sheafPushforwardContinuous (A := A)).IsRightAdjoint] :
    Sheaf Y.siteTopology A ⥤ Sheaf X.siteTopology A :=
  @Functor.sheafPullback _ _ _ _ f.base A _ Y.siteTopology X.siteTopology
    f.isMorphismOfSites.toIsContinuous inferInstance

/-- Sheaf pullback is left adjoint to continuous pushforward along a ringed-site map. -/
noncomputable abbrev sheafAdjunctionContinuous
    {A : Type u} [Category.{v} A] (f : Hom X Y)
    [(f.sheafPushforwardContinuous (A := A)).IsRightAdjoint] :
    f.sheafPullback (A := A) ⊣ f.sheafPushforwardContinuous (A := A) :=
  @Functor.sheafAdjunctionContinuous _ _ _ _ f.base A _ Y.siteTopology X.siteTopology
    f.isMorphismOfSites.toIsContinuous inferInstance

/-- The identity morphism of a ringed site. -/
noncomputable def id (X : RingedSite.{uX, vX, w}) : Hom X X :=
  CategoryTheory.RingedSiteMap.id X.siteTopology X.structureSheaf

/-- Composition of morphisms of ringed sites. -/
noncomputable def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  CategoryTheory.RingedSiteMap.comp f g

end Hom

end RingedSite

