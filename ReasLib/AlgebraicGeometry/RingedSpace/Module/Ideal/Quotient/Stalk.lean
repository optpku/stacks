/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Sheaves.Sheafify
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.Topology.Sheaves.Stalks.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of quotient structure sheaves

For an ideal sheaf `I` on a ringed space, this file constructs the comparison between the stalk
of the sectionwise quotient presheaf and the quotient of the structure-sheaf stalk by the image
of `I_x`.  The construction is given by explicit neighborhood legs and quotient lifts.  It is
then transported across the canonical sheafification-unit stalk isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient

variable {X : RingedSpace.{u}}

/-- The sectionwise quotient presheaf specialized to the topology of a ringed space. -/
@[stacks 0H2K "sectionwise quotient presheaf"]
noncomputable abbrev presheaf
    (I : X.IdealSubobject) :
    TopCat.Presheaf CommRingCat.{u} X :=
  SheafOfModules.RingedSite.IdealSheaf.Quotient.presheaf
    (J := Opens.grothendieckTopology X) (O := X.sheaf) I

/-- The quotient sheaf specialized to a ringed space. -/
@[stacks 0H2K "quotient sheaf"]
noncomputable abbrev sheaf
    (I : X.IdealSubobject) :
    TopCat.Sheaf CommRingCat.{u} X :=
  SheafOfModules.RingedSite.IdealSheaf.Quotient.sheaf
    (J := Opens.grothendieckTopology X) (O := X.sheaf) I

/-- The quotient projection specialized to a ringed space. -/
@[stacks 0H2K "quotient sheaf projection"]
noncomputable abbrev projection
    (I : X.IdealSubobject) :
    X.sheaf ⟶ sheaf I :=
  SheafOfModules.RingedSite.IdealSheaf.Quotient.projection
    (J := Opens.grothendieckTopology X) (O := X.sheaf) I

/-- The stalk of the sectionwise quotient presheaf before sheafification. -/
@[stacks 0H2K "raw quotient-presheaf stalk"]
noncomputable abbrev rawStalk
    (I : X.IdealSubobject) (x : X) :
    CommRingCat.{u} :=
  (presheaf I).stalk x

/-- The stalk of the sheafified quotient. -/
@[stacks 0H2K "quotient sheaf stalk"]
noncomputable abbrev sheafStalk
    (I : X.IdealSubobject) (x : X) :
    CommRingCat.{u} :=
  TopCat.Presheaf.stalk (X := (X : TopCat.{u})) (sheaf I).obj x

/-- The quotient of the structure-sheaf stalk by the image of the ideal-sheaf stalk. -/
@[stacks 0H2K "quotient of the structure-sheaf stalk"]
noncomputable abbrev stalkQuotient
    (I : X.IdealSubobject) (x : X) :=
  X.presheaf.stalk x ⧸ idealSheafStalkIdeal I x

/-- Germs send the section ideal on a neighborhood into the image ideal of the ideal-sheaf
stalk. -/
@[stacks 0H2K "section ideal maps to the stalk ideal"]
theorem sections_le_comap_germ
    (I : X.IdealSubobject)
    (x : X) (U : Opens X) (hx : x ∈ U) :
    SheafOfModules.RingedSite.IdealSheaf.sections I (op U) ≤
      (idealSheafStalkIdeal I x).comap (X.presheaf.germ U x hx).hom := sorry

/-- The composite from a neighborhood ring to the quotient stalk kills its section ideal. -/
@[stacks 0H2K "quotient stalk germ vanishing"]
theorem quotientGerm_eq_zero
    (I : X.IdealSubobject)
    (x : X) (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U))
    (hr : r ∈ SheafOfModules.RingedSite.IdealSheaf.sections I (op U)) :
    ((Ideal.Quotient.mk (idealSheafStalkIdeal I x)).comp
      (X.presheaf.germ U x hx).hom) r = 0 := sorry

/-- The map from a neighborhood's sectionwise quotient to the quotient of the stalk ring. -/
@[stacks 0H2K "raw quotient-stalk neighborhood leg"]
noncomputable def rawLeg
    (I : X.IdealSubobject)
    (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      presheaf I).obj U) ⟶
      CommRingCat.of (stalkQuotient I x) :=
  CommRingCat.ofHom <| Ideal.Quotient.lift
    (SheafOfModules.RingedSite.IdealSheaf.sections I (op U.unop.1))
    ((Ideal.Quotient.mk (idealSheafStalkIdeal I x)).comp
      (X.presheaf.germ U.unop.1 x U.unop.2).hom)
    (quotientGerm_eq_zero I x U.unop.1 U.unop.2)

/-- A neighborhood leg sends the class of a section to the class of its germ. -/
@[stacks 0H2K "quotient-stalk comparison on neighborhood classes"]
theorem rawLeg_mk
    (I : X.IdealSubobject)
    (x : X) (U : (OpenNhds x)ᵒᵖ) (r : X.presheaf.obj (op U.unop.1)) :
    rawLeg I x U
        (Ideal.Quotient.mk
          (SheafOfModules.RingedSite.IdealSheaf.sections I (op U.unop.1)) r) =
      Ideal.Quotient.mk (idealSheafStalkIdeal I x)
        (X.presheaf.germ U.unop.1 x U.unop.2 r) := sorry

/-- The neighborhood quotient maps are compatible with restriction. -/
@[stacks 0H2K "raw quotient-stalk leg naturality"]
theorem rawLeg_naturality
    (I : X.IdealSubobject)
    (x : X) {U V : (OpenNhds x)ᵒᵖ} (f : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
        presheaf I).map f) ≫
        rawLeg I x V =
      rawLeg I x U := sorry

/-- The cocone from neighborhood quotients to the quotient of the stalk ring. -/
@[stacks 0H2K "raw quotient-stalk cocone"]
noncomputable def rawCocone
    (I : X.IdealSubobject) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙
      presheaf I) where
  pt := CommRingCat.of (stalkQuotient I x)
  ι :=
    { app := rawLeg I x
      naturality := fun _ _ f ↦ rawLeg_naturality I x f }

/-- The canonical map from the raw quotient-presheaf stalk to `𝒪_{X,x} / I_x`. -/
@[stacks 0H2K "raw quotient-presheaf stalk comparison"]
noncomputable def rawToQuotient
    (I : X.IdealSubobject) (x : X) :
    rawStalk I x ⟶ CommRingCat.of (stalkQuotient I x) :=
  colimit.desc _ (rawCocone I x)

/-- The presheaf quotient projection on stalks. -/
@[stacks 0H2K "raw quotient projection on stalks"]
noncomputable abbrev rawProjectionStalk
    (I : X.IdealSubobject) (x : X) :
    X.presheaf.stalk x ⟶ rawStalk I x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (SheafOfModules.RingedSite.IdealSheaf.Quotient.presheafProjection
      (J := Opens.grothendieckTopology X) (O := X.sheaf) I)

/-- The image ideal of `I_x` is killed by the raw quotient projection on stalks. -/
@[stacks 0H2K "raw quotient projection kills the stalk ideal"]
theorem rawProjectionStalk_eq_zero
    (I : X.IdealSubobject)
    (x : X) (r : X.presheaf.stalk x) (hr : r ∈ idealSheafStalkIdeal I x) :
    rawProjectionStalk I x r = 0 := sorry

/-- The quotient lift from `𝒪_{X,x} / I_x` to the stalk of the raw quotient presheaf. -/
@[stacks 0H2K "inverse raw quotient-stalk comparison"]
noncomputable def quotientToRaw
    (I : X.IdealSubobject) (x : X) :
    stalkQuotient I x →+* rawStalk I x :=
  Ideal.Quotient.lift (idealSheafStalkIdeal I x)
    (rawProjectionStalk I x).hom (rawProjectionStalk_eq_zero I x)

/-- The raw comparison followed by its quotient lift is the identity. -/
@[simp, stacks 0H2K "raw quotient-stalk comparison forward-inverse law"]
theorem rawToQuotient_comp_quotientToRaw
    (I : X.IdealSubobject) (x : X) :
    (rawToQuotient I x).hom.comp (quotientToRaw I x) =
      RingHom.id (stalkQuotient I x) := sorry

/-- The quotient lift followed by the raw comparison is the identity. -/
@[simp, stacks 0H2K "raw quotient-stalk comparison inverse-forward law"]
theorem quotientToRaw_comp_rawToQuotient
    (I : X.IdealSubobject) (x : X) :
    (quotientToRaw I x).comp (rawToQuotient I x).hom =
      RingHom.id (rawStalk I x) := sorry

/-- The stalk of the sectionwise quotient presheaf is canonically the quotient of the structure
stalk by the image ideal `I_x`. -/
@[stacks 0H2K "raw quotient-presheaf stalk equivalence"]
noncomputable def rawStalkEquiv
    (I : X.IdealSubobject) (x : X) :
    rawStalk I x ≃+* stalkQuotient I x :=
  RingEquiv.ofRingHom (rawToQuotient I x).hom (quotientToRaw I x)
    (rawToQuotient_comp_quotientToRaw I x)
    (quotientToRaw_comp_rawToQuotient I x)

/-- The sheafification unit induces a morphism from the raw quotient stalk to the quotient-sheaf
stalk. -/
@[stacks 0D09 "quotient-presheaf sheafification on stalks"]
noncomputable abbrev sheafificationStalk
    (I : X.IdealSubobject) (x : X) :
    rawStalk I x ⟶ sheafStalk I x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (presheaf I))

/-- The inverse is inherited from the reusable topological sheafification-stalk API.  Naming it
here keeps the quotient-stalk interface independent of any `IsIso` implementation detail. -/
@[stacks 0D09 "quotient-presheaf sheafification inverse on stalks"]
noncomputable abbrev sheafificationStalkInv
    (I : X.IdealSubobject) (x : X) :
    sheafStalk I x ⟶ rawStalk I x :=
  TopCat.Presheaf.SheafificationStalk.comparisonInv (presheaf I) x

/-- The two explicit sheafification-stalk maps are inverse to one another. -/
@[simp, stacks 0D09 "quotient-presheaf sheafification stalk forward-inverse law"]
theorem sheafificationStalk_comp_sheafificationStalkInv
    (I : X.IdealSubobject) (x : X) :
    sheafificationStalk I x ≫ sheafificationStalkInv I x = 𝟙 _ := sorry

/-- The inverse map is also a left inverse of the sheafification-stalk comparison. -/
@[simp, stacks 0D09 "quotient-presheaf sheafification stalk inverse-forward law"]
theorem sheafificationStalkInv_comp_sheafificationStalk
    (I : X.IdealSubobject) (x : X) :
    sheafificationStalkInv I x ≫ sheafificationStalk I x = 𝟙 _ := sorry

/-- The sheafification-stalk comparison as literal categorical isomorphism data. -/
@[stacks 0D09 "quotient-presheaf sheafification stalk isomorphism"]
noncomputable def sheafificationStalkIso
    (I : X.IdealSubobject) (x : X) :
    rawStalk I x ≅ sheafStalk I x where
  hom := sheafificationStalk I x
  inv := sheafificationStalkInv I x
  hom_inv_id := sheafificationStalk_comp_sheafificationStalkInv I x
  inv_hom_id := sheafificationStalkInv_comp_sheafificationStalk I x

/-- The forward leg of the literal sheafification-stalk isomorphism. -/
@[simp, stacks 0D09 "quotient-presheaf sheafification stalk isomorphism hom"]
theorem sheafificationStalkIso_hom
    (I : X.IdealSubobject) (x : X) :
    (sheafificationStalkIso I x).hom = sheafificationStalk I x := sorry

/-- The inverse leg of the literal sheafification-stalk isomorphism. -/
@[simp, stacks 0D09 "quotient-presheaf sheafification stalk isomorphism inverse"]
theorem sheafificationStalkIso_inv
    (I : X.IdealSubobject) (x : X) :
    (sheafificationStalkIso I x).inv = sheafificationStalkInv I x := sorry

/-- The explicit ring equivalence induced on stalks by sheafification. -/
@[stacks 0D09 "quotient-presheaf sheafification stalk equivalence"]
noncomputable def sheafificationStalkEquiv
    (I : X.IdealSubobject) (x : X) :
    rawStalk I x ≃+* sheafStalk I x :=
  (sheafificationStalkIso I x).commRingCatIsoToRingEquiv

/-- The stalk of `𝒪_X / I` is canonically `𝒪_{X,x} / I_x`. -/
@[stacks 0H2K "quotient sheaf stalk equivalence"]
noncomputable def stalkEquiv
    (I : X.IdealSubobject) (x : X) :
    sheafStalk I x ≃+* stalkQuotient I x :=
  (sheafificationStalkEquiv I x).symm.trans (rawStalkEquiv I x)

/-- The quotient-sheaf projection on stalks. -/
@[stacks 0H2K "quotient sheaf projection on stalks"]
noncomputable abbrev projectionStalk
    (I : X.IdealSubobject) (x : X) :
    X.presheaf.stalk x ⟶ sheafStalk I x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (projection I).hom

/-- The stalk of a module descended to `𝒪_X / I`, retaining its canonical module structure over
the quotient-sheaf stalk. -/
@[stacks 0H2K "stalk of a descended quotient module"]
noncomputable abbrev descendStalk
    (I : X.IdealSubobject)
    (F : X.Modules)
    (h : SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (J := Opens.grothendieckTopology X) (O := X.sheaf) I F) (x : X) :
    ModuleCat (sheafStalk I x) :=
  (SheafOfModules.stalkFunctorOfCommRing (sheaf I) x).obj
    (SheafOfModules.RingedSite.IdealSheaf.Quotient.descend I F h)

/-- The additive stalk map from a descended quotient module back to the stalk of its original
underlying module sheaf. -/
@[stacks 0H2K "underlying additive map of a descended module stalk"]
noncomputable abbrev descendStalkForget
    (I : X.IdealSubobject)
    (F : X.Modules)
    (h : SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (J := Opens.grothendieckTopology X) (O := X.sheaf) I F) (x : X) :
    descendStalk I F h x →+ RingedSpace.stalkModuleCat F x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (SheafOfModules.RingedSite.IdealSheaf.Quotient.forgetIso I F h).hom.hom).hom

/-- On stalks, pulling the descended scalar action back along `𝒪_X ⟶ 𝒪_X / I` recovers the
original `𝒪_{X,x}`-action. -/
@[stacks 0H2K "descended module stalk scalar action"]
theorem descendStalkForget_smul_projection
    (I : X.IdealSubobject)
    (F : X.Modules)
    (h : SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (J := Opens.grothendieckTopology X) (O := X.sheaf) I F)
    (x : X) (r : X.presheaf.stalk x) (m : descendStalk I F h x) :
    descendStalkForget I F h x (projectionStalk I x r • m) =
      r • descendStalkForget I F h x m := sorry

/-- Under `stalkEquiv`, the stalk map of the quotient projection is the ordinary quotient map. -/
@[stacks 0H2K "quotient projection on stalks"]
theorem stalkEquiv_projectionStalk
    (I : X.IdealSubobject)
    (x : X) (r : X.presheaf.stalk x) :
    stalkEquiv I x (projectionStalk I x r) =
      Ideal.Quotient.mk (idealSheafStalkIdeal I x) r := sorry

/-- Under `stalkEquiv`, the germ of a projected local section is the class of its original
germ. -/
@[stacks 0H2K "quotient projection on germs"]
theorem stalkEquiv_germ_projection
    (I : X.IdealSubobject)
    (x : X) (U : Opens X) (hx : x ∈ U) (r : X.presheaf.obj (op U)) :
    stalkEquiv I x
        (TopCat.Presheaf.germ (X := (X : TopCat.{u})) (sheaf I).obj U x hx
          ((projection I).hom.app (op U) r)) =
      Ideal.Quotient.mk (idealSheafStalkIdeal I x)
        (X.presheaf.germ U x hx r) := sorry

-- The maps and equivalences are explicit. Any `sorryAx` below is confined to ideal-containment,
-- naturality, quotient-lift well-definedness, or inverse-law proof fields.

end AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient
