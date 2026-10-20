/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Torsors and first sheaf cohomology

This file constructs the canonical map from isomorphism classes of torsors under an abelian
sheaf to its first cohomology group.  The construction linearizes the torsor, imposes the action
relations by a cokernel, and takes the resulting fixed-endpoint extension class.
-/

@[expose] public section

open CategoryTheory Opposite Limits

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.Torsor.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- The constant integer sheaf used as the quotient of a torsor extension. -/
abbrev integerSheaf : Sheaf J AddCommGrpCat.{max u v} :=
  constantIntegerSheaf J

/-- The underlying type-valued sheaf of an additive sheaf. -/
abbrev underlyingType (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafForget J).obj H

/-- Free abelianization followed by sheafification. -/
abbrev linearization (G : Sheaf J (Type (max u v))) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj G

/-- The morphism out of `linearization G` induced by a map from `G` to an underlying
type-valued additive sheaf. -/
noncomputable def linearizationLift {G : Sheaf J (Type (max u v))}
    {A : Sheaf J AddCommGrpCat.{max u v}} (f : G ⟶ underlyingType A) :
    linearization G ⟶ A :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv G A).symm f

/-- The objectwise product whose sections encode an acting section and a torsor section. -/
def relationObject (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (U : Cᵒᵖ) : Type (max u v) :=
  H.1.obj U × P.carrier.1.obj U

/-- Restriction on the objectwise product used to impose the torsor action relation. -/
def relationMap (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    relationObject H P X ⟶ relationObject H P Y :=
  TypeCat.ofHom fun x =>
    ((H.1.map f) x.1, (P.carrier.1.map f) x.2)

/-- Restriction on `relationObject` preserves identity morphisms. -/
theorem relationMap_id (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (X : Cᵒᵖ) :
    relationMap H P (𝟙 X) = 𝟙 (relationObject H P X) := sorry

/-- Restriction on `relationObject` preserves composition. -/
theorem relationMap_comp (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relationMap H P (f ≫ g) = relationMap H P f ≫ relationMap H P g := sorry

/-- The presheaf of pairs consisting of an acting section and a torsor section. -/
def relationPresheaf (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : Cᵒᵖ ⥤ Type (max u v) where
  obj := relationObject H P
  map := relationMap H P
  map_id := relationMap_id H P
  map_comp := relationMap_comp H P

/-- The relation presheaf is a sheaf. -/
theorem relationPresheaf_isSheaf (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    Presheaf.IsSheaf J (relationPresheaf H P) := sorry

/-- The type-valued sheaf carrying the action relation of a torsor. -/
@[stacks 03AJ "torsor relation source"]
def relationSource (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : Sheaf J (Type (max u v)) :=
  ⟨relationPresheaf H P, relationPresheaf_isSheaf H P⟩

/-- The first projection from the relation source, objectwise. -/
def relationFstApp (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (U : Cᵒᵖ) :
    (relationSource H P).1.obj U ⟶ (underlyingType H).1.obj U :=
  TypeCat.ofHom fun x => x.1

/-- The first projections from the relation source commute with restriction. -/
theorem relationFst_naturality (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relationSource H P).1.map f ≫ relationFstApp H P Y =
      relationFstApp H P X ≫ (underlyingType H).1.map f := sorry

/-- The first projection from the relation source to the acting sheaf. -/
def relationFst (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    relationSource H P ⟶ underlyingType H :=
  { hom :=
      { app := relationFstApp H P
        naturality := fun {X Y} f => relationFst_naturality H P (X := X) (Y := Y) f } }

/-- The second projection from the relation source, objectwise. -/
def relationSndApp (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (U : Cᵒᵖ) :
    (relationSource H P).1.obj U ⟶ P.carrier.1.obj U :=
  TypeCat.ofHom fun x => x.2

/-- The second projections from the relation source commute with restriction. -/
theorem relationSnd_naturality (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relationSource H P).1.map f ≫ relationSndApp H P Y =
      relationSndApp H P X ≫ P.carrier.1.map f := sorry

/-- The second projection from the relation source to the torsor carrier. -/
def relationSnd (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : relationSource H P ⟶ P.carrier :=
  { hom :=
      { app := relationSndApp H P
        naturality := fun {X Y} f => relationSnd_naturality H P (X := X) (Y := Y) f } }

/-- Applying the acting section to the torsor section, objectwise. -/
noncomputable def actionApp (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (U : Cᵒᵖ) :
    (relationSource H P).1.obj U ⟶ P.carrier.1.obj U :=
  TypeCat.ofHom fun x =>
    (PseudoTorsor.opMulAction P.toPseudoTorsor U).smul x.1 x.2

/-- The torsor action maps commute with restriction. -/
theorem actionMap_naturality (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relationSource H P).1.map f ≫ actionApp H P Y =
      actionApp H P X ≫ P.carrier.1.map f := sorry

/-- The action morphism from the relation source to the torsor carrier. -/
noncomputable def actionMap (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : relationSource H P ⟶ P.carrier :=
  { hom :=
      { app := actionApp H P
        naturality := fun {X Y} f => actionMap_naturality H P (X := X) (Y := Y) f } }

/-- The objectwise map sending every torsor section to `1` in the constant integer sheaf. -/
noncomputable def integerSectionApp (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) (U : Cᵒᵖ) :
    P.carrier.1.obj U ⟶ (underlyingType (integerSheaf (J := J))).1.obj U :=
  TypeCat.ofHom fun _ => Sheaf.constantIntegerSheafOne J U

/-- The objectwise maps to `1` commute with restriction. -/
theorem integerSectionMap_naturality (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    P.carrier.1.map f ≫ integerSectionApp H P Y =
      integerSectionApp H P X ≫ (underlyingType (integerSheaf (J := J))).1.map f := sorry

/-- The sheaf morphism sending every torsor section to `1`. -/
noncomputable def integerSectionMap (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    P.carrier ⟶ underlyingType (integerSheaf (J := J)) :=
  { hom :=
      { app := integerSectionApp H P
        naturality := fun {X Y} f =>
          integerSectionMap_naturality H P (X := X) (Y := Y) f } }

/-- The linearized relation `(h, p) ↦ (h, p - h • p)` used in the torsor extension. -/
@[stacks 03AJ "linearized torsor relation"]
noncomputable def relation (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    linearization (relationSource H P) ⟶ H ⊞ linearization P.carrier :=
  linearizationLift (relationFst H P) ≫ biprod.inl +
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (relationSnd H P) ≫ biprod.inr -
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (actionMap H P) ≫ biprod.inr

/-- The augmentation of the linearized torsor carrier to the constant integer sheaf. -/
noncomputable def augmentation (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    linearization P.carrier ⟶ integerSheaf (J := J) :=
  linearizationLift (integerSectionMap H P)

/-- The torsor relation is killed by the map induced by the augmentation. -/
theorem relation_comp_augmentation (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    relation H P ≫ biprod.desc 0 (augmentation H P) = 0 := sorry

/-- The middle object of the extension associated to a torsor. -/
noncomputable def middle (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : Sheaf J AddCommGrpCat.{max u v} :=
  cokernel (relation H P)

/-- The inclusion of the acting sheaf into the middle object of the torsor extension. -/
noncomputable def inclusion (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : H ⟶ middle H P :=
  biprod.inl ≫ cokernel.π (relation H P)

/-- The projection from the middle object of the torsor extension to the constant integer
sheaf. -/
noncomputable def projection (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : middle H P ⟶ integerSheaf (J := J) :=
  cokernel.desc (relation H P) (biprod.desc 0 (augmentation H P))
    (relation_comp_augmentation H P)

/-- The inclusion and projection of the torsor extension compose to zero. -/
theorem inclusion_comp_projection (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    inclusion H P ≫ projection H P = 0 := sorry

/-- The short complex with fixed endpoints associated to the torsor by its cokernel relation. -/
@[stacks 03AJ "extension associated to a torsor"]
noncomputable def extension (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) : ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
  ShortComplex.mk (inclusion H P) (projection H P) (inclusion_comp_projection H P)

/-- The short complex underlying the torsor extension is exact. -/
theorem extension_shortExact (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    (extension H P).ShortExact := sorry

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max u v})]

/-- Isomorphic torsors determine equal canonical Ext classes of their fixed-endpoint short complexes. -/
theorem extension_extClass_eq_of_iso (H : Sheaf J AddCommGrpCat.{max u v})
    {P Q : Torsor (Sheaf.toSheafOfGroups H)} (e : Torsor.Iso P Q) :
    (extension_shortExact H P).extClass = (extension_shortExact H Q).extClass := sorry

/-- The canonical map from isomorphism classes of torsors under an abelian sheaf to its first
cohomology group, sending a representative torsor to the `Ext¹` class of its explicit cokernel
extension. -/
@[stacks 03AJ "torsor class map"]
noncomputable def classMap (H : Sheaf J AddCommGrpCat.{max u v}) :
    Torsor.IsoClasses (Sheaf.toSheafOfGroups H) → Sheaf.H H 1 :=
  _root_.Quotient.lift
    (fun P => (extension_shortExact H P).extClass)
    (fun _ _ hPQ => hPQ.elim fun e =>
      extension_extClass_eq_of_iso H e)

/-- The torsor-class map computes as the extension class on a representative. -/
@[simp]
theorem classMap_apply (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Torsor (Sheaf.toSheafOfGroups H)) :
    classMap H (_root_.Quotient.mk'' P) =
      (extension_shortExact H P).extClass := sorry

/-- The trivial torsor maps to zero in first cohomology. -/
@[simp]
theorem classMap_trivial (H : Sheaf J AddCommGrpCat.{max u v}) :
    classMap H (_root_.Quotient.mk'' (Torsor.trivial (Sheaf.toSheafOfGroups H))) = 0 := sorry

/-- The canonical map from isomorphism classes of torsors under an abelian sheaf `H` to
`H.H 1` is bijective. -/
@[stacks 03AJ "torsors classified by first cohomology"]
theorem classMap_bijective (H : Sheaf J AddCommGrpCat.{max u v}) :
    Function.Bijective (classMap H) := sorry

end CategoryTheory.Sheaf.Torsor.Cohomology
