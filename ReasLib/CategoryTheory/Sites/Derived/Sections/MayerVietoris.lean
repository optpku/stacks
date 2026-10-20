/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Cover
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.MappingCocone.Triangle
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mayer--Vietoris maps for derived sections

This leaf owns the canonical restriction maps and the two-term Mayer--Vietoris row attached to a
square in a site. Chapter files only reuse these declarations; derived comparison models and
K-injective calculations belong to their own reusable leaves.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)]

-- Local instance justification (search instability): Mathlib's explicit warning in
-- CategoryTheory/Abelian/Basic.lean notes that global registration breaks ModuleCat, Sheaf, and Free.
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The abelian-group-valued sections functor with its coefficient universe made explicit. -/
abbrev sectionsFunctor (U : C) :
    Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  siteAbelianSectionsFunctor J U

/-- The cochain-level sections functor used to construct derived restrictions. -/
@[stacks 0EVY "cochain sections functor for Mayer--Vietoris"]
abbrev sectionsToDerived (U : C) :
    CochainComplex (SiteAbelianSheafCat J) ℤ ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  Functor.RightDerived.Cochain.toDerived (sectionsFunctor J U)

/-- Restriction of abelian-group-valued sections along `φ : U ⟶ V`. -/
@[stacks 0EVY "sections restriction"]
abbrev restriction {U V : C} (φ : U ⟶ V) :
    sectionsFunctor J V ⟶ sectionsFunctor J U :=
  Functor.whiskerLeft
    (sheafToPresheaf J AddCommGrpCat.{max u v})
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).map φ.op)

/-- The cochain-level restriction induced by `φ : U ⟶ V`. -/
@[stacks 0EVY "cochain sections restriction"]
abbrev restrictionToDerived {U V : C} (φ : U ⟶ V) :
    sectionsToDerived J V ⟶ sectionsToDerived J U :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (restriction J φ) (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- The canonical derived restriction `RΓ[J](V) ⟶ RΓ[J](U)`. -/
@[stacks 0EVY "derived sections restriction"]
abbrev restrictionDerived {U V : C} (φ : U ⟶ V) :
    RΓ[J](V) ⟶ RΓ[J](U) :=
  Functor.rightDerivedNatTrans
    (RΓ[J](V))
    (RΓ[J](U))
    (Functor.RightDerived.Cochain.unit (sectionsFunctor J V))
    (Functor.RightDerived.Cochain.unit (sectionsFunctor J U))
    (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) :
      MorphismProperty (CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ))
    (restrictionToDerived J φ)

/-- Equal sheafified-representable maps induce equal derived restriction maps. -/
@[stacks 0EVY "restriction invariance"]
theorem restrictionDerived_eq_of_sheafifiedRepresentableMap_eq
    {U V : C} {φ ψ : U ⟶ V}
    (hφψ : J.sheafifiedRepresentableMap φ = J.sheafifiedRepresentableMap ψ) :
    restrictionDerived J φ = restrictionDerived J ψ := sorry

/-- Derived restrictions compose contravariantly. -/
@[stacks 0EVY "restriction composition"]
theorem restrictionDerived_comp
    {U V W : C} (φ : U ⟶ V) (ψ : V ⟶ W) :
    restrictionDerived J ψ ≫ restrictionDerived J φ =
      restrictionDerived J (φ ≫ ψ) := sorry

/-- The first Mayer--Vietoris map into the canonical biproduct of derived sections. -/
@[stacks 0EVY "Mayer--Vietoris first map"]
abbrev toBiprod {X Y Z : C} (inY : Y ⟶ X) (inZ : Z ⟶ X) :
    RΓ[J](X) ⟶ (RΓ[J](Z) ⊞ RΓ[J](Y)) :=
  biprod.lift (restrictionDerived J inZ) (restrictionDerived J inY)

/-- The second Mayer--Vietoris difference map from the biproduct to overlap sections. -/
@[stacks 0EVY "Mayer--Vietoris difference map"]
abbrev difference {Y Z E : C} (f : E ⟶ Y) (g : E ⟶ Z) :
    (RΓ[J](Z) ⊞ RΓ[J](Y)) ⟶ RΓ[J](E) :=
  biprod.desc (restrictionDerived J g) (-restrictionDerived J f)

/-- The canonical Mayer--Vietoris row is a complex when the sheafified representables form a
pushout square. -/
@[stacks 0EVY "Mayer--Vietoris row is a complex"]
theorem toBiprod_comp_difference
    {X Y Z E : C} (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ)) :
    toBiprod J inY inZ ≫ difference J f g = 0 := sorry

/-- A pushout square with a monomorphic overlap admits a functorial distinguished
Mayer--Vietoris triangle of derived sections. -/
@[stacks 0EVY "functorial Mayer--Vietoris triangle"]
theorem exists_triangle
    {X Y Z E : C} (f : E ⟶ Y) (g : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (hpushout :
      IsPushout
        (J.sheafifiedRepresentableMap f)
        (J.sheafifiedRepresentableMap g)
        (J.sheafifiedRepresentableMap inY)
        (J.sheafifiedRepresentableMap inZ))
    (hmono : Mono (J.sheafifiedRepresentableMap f)) :
    ∃ delta : RΓ[J](E) ⟶
        RΓ[J](X) ⋙ shiftFunctor (DerivedCategory AddCommGrpCat.{max u v}) (1 : ℤ),
      ∀ K : DerivedCategory (SiteAbelianSheafCat J),
        Triangle.mk
            ((toBiprod J inY inZ).app K)
            ((difference J f g).app K)
            (delta.app K) ∈
          distTriang (DerivedCategory AddCommGrpCat.{max u v}) := sorry

/-- A commutative square in a category, bundled in the orientation used by Mayer--Vietoris
restriction maps. -/
structure Square (C : Type u) [Category.{v} C] where
  /-- The overlap object. -/
  E : C
  /-- The first object covering the target. -/
  Y : C
  /-- The second object covering the target. -/
  Z : C
  /-- The target object. -/
  X : C
  /-- The overlap map to `Y`. -/
  toY : E ⟶ Y
  /-- The overlap map to `Z`. -/
  toZ : E ⟶ Z
  /-- The map from `Y` to the target. -/
  inY : Y ⟶ X
  /-- The map from `Z` to the target. -/
  inZ : Z ⟶ X
  /-- Commutativity of the square. -/
  comm : toY ≫ inY = toZ ≫ inZ

namespace Square

/-- Bundle four maps and their commutative-square witness as a Mayer--Vietoris square. -/
def ofCommSq {C : Type u} [Category.{v} C]
    {E Y Z X : C} (toY : E ⟶ Y) (toZ : E ⟶ Z)
    (inY : Y ⟶ X) (inZ : Z ⟶ X)
    (h : CommSq toY toZ inY inZ) : Square C where
  E := E
  Y := Y
  Z := Z
  X := X
  toY := toY
  toZ := toZ
  inY := inY
  inZ := inZ
  comm := h.w

/-- The first derived-section map associated with a bundled square. -/
abbrev toBiprod (S : Square C) :
    RΓ[J](S.X) ⟶ (RΓ[J](S.Z) ⊞ RΓ[J](S.Y)) :=
  MayerVietoris.toBiprod J S.inY S.inZ

/-- The second derived-section map associated with a bundled square. -/
abbrev difference (S : Square C) :
    (RΓ[J](S.Z) ⊞ RΓ[J](S.Y)) ⟶ RΓ[J](S.E) :=
  MayerVietoris.difference J S.toY S.toZ

/-- A cochain model realizing the canonical Mayer--Vietoris row for `S` at `K`. -/
structure Realization (S : Square C)
    (K : DerivedCategory (SiteAbelianSheafCat J)) where
  /-- The single cochain complex representing the derived sheaf. -/
  complex : CochainComplex (SiteAbelianSheafCat J) ℤ
  /-- The chosen complex is K-injective. -/
  isKInjective : complex.IsKInjective
  /-- The chosen complex represents the derived object. -/
  represents : DerivedCategory.Q.obj complex ≅ K

namespace Realization

/-- The section complex obtained from one representative over an object. -/
noncomputable def sectionComplex (R : Realization J S K) (U : C) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  ((sectionsFunctor J U).mapHomologicalComplex (ComplexShape.up ℤ)).obj R.complex

/-- The cochain restriction map induced by a morphism of site objects. -/
noncomputable def restrictionMap (R : Realization J S K) {U V : C} (φ : U ⟶ V) :
    sectionComplex J R V ⟶ sectionComplex J R U :=
  (NatTrans.mapHomologicalComplex (restriction J φ) (ComplexShape.up ℤ)).app R.complex

/-- The two cochain maps in the canonical section row compose to zero. -/
theorem cochain_comp_zero (R : Realization J S K) :
    biprod.lift (restrictionMap (J := J) R S.inZ) (restrictionMap (J := J) R S.inY) ≫
        biprod.desc (restrictionMap (J := J) R S.toZ)
          (-restrictionMap (J := J) R S.toY) = 0 := sorry

/-- The canonical cochain row of sections associated to a realization. -/
noncomputable def row (R : Realization J S K) :
    ShortComplex (CochainComplex AddCommGrpCat.{max u v} ℤ) :=
  ShortComplex.mk
    (biprod.lift (restrictionMap (J := J) R S.inZ) (restrictionMap (J := J) R S.inY))
    (biprod.desc (restrictionMap (J := J) R S.toZ) (-restrictionMap (J := J) R S.toY))
    (cochain_comp_zero (J := J) R)

/-- Construct a realization from an explicit K-injective representative. -/
noncomputable def ofKInjective (I : CochainComplex (SiteAbelianSheafCat J) ℤ)
    (hI : I.IsKInjective) (e : DerivedCategory.Q.obj I ≅ K) : Realization J S K :=
  { complex := I
    isKInjective := hI
    represents := e }

/-- The constructor records exactly the selected representative and its derived identification. -/
theorem ofKInjective_spec (I : CochainComplex (SiteAbelianSheafCat J) ℤ)
    (hI : I.IsKInjective) (e : DerivedCategory.Q.obj I ≅ K) :
    (ofKInjective (J := J) (S := S) (K := K) I hI e).complex = I ∧
      (ofKInjective (J := J) (S := S) (K := K) I hI e).represents = e := sorry

/-- The zero-cochain lift from the section row to its mapping cocone. -/
noncomputable def cochainComparison (R : Realization J S K) :
    R.row.X₁ ⟶ CochainComplex.mappingCocone R.row.g :=
  CochainComplex.mappingCocone.lift R.row.g R.row.f
    (0 : CochainComplex.HomComplex.Cochain R.row.X₁ R.row.X₃ (-1))
    (CategoryTheory.DerivedCategory.MappingCocone.zeroLiftCondition
      R.row.f R.row.g R.row.zero)

/-- The derived comparison map attached to a coherent cochain realization. -/
noncomputable def comparison (R : Realization J S K) :
    DerivedCategory.Q.obj R.row.X₁ ⟶
      DerivedCategory.Q.obj (CochainComplex.mappingCocone R.row.g) :=
  DerivedCategory.Q.map R.cochainComparison

end Realization

/-- The canonical Mayer--Vietoris condition is invertibility of every coherent comparison. -/
@[stacks 0F18 "canonical Mayer--Vietoris condition"]
def Condition (S : Square C) (K : DerivedCategory (SiteAbelianSheafCat J)) : Prop :=
  ∀ R : Realization J S K, IsIso R.comparison

namespace Realization

/-- The representation-independent condition is equivalent to invertibility of the canonical
comparison attached to any cochain realization. -/
theorem condition_iff_comparison_isIso (R : Realization J S K) :
    S.Condition J K ↔ IsIso R.comparison := sorry

/-- A short exact cochain realization supplies the representation-independent
Mayer--Vietoris condition. -/
theorem condition_of_shortExact (R : Realization J S K) (hR : R.row.ShortExact) :
    S.Condition J K := sorry

/-- The comparison attached to a short exact cochain realization is an isomorphism. -/
theorem comparison_isIso_of_shortExact
    (R : Realization J S K) (hR : R.row.ShortExact) :
    IsIso R.comparison := sorry

end Realization

end Square

end

end CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

end
