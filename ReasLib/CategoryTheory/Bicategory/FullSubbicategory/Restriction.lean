/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting category equivalences to full subbicategories

A strict bicategory has an underlying ordinary category.  This file supplies the ordinary
category interface of an object-property full subbicategory and uses it to restrict an ambient
category equivalence.  The construction keeps the ambient functors and their unit and counit as
explicit data; only property transport and functoriality laws are proof-valued.
-/

@[expose] public section

universe w v vA u uA

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace ObjectProperty.FullSubbicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {D : Type u} [Bicategory.{w, v} D] [Bicategory.Strict D]
variable {P : ObjectProperty D} {X Y Z : P.FullSubbicategory}

/-- Lift an ambient morphism to the underlying ordinary category of a full subbicategory. -/
abbrev homMk (f : X.1 ⟶ Y.1) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom f

/-- The ambient representative of a lifted ordinary morphism is the supplied morphism. -/
@[simp]
theorem homMk_hom (f : X.1 ⟶ Y.1) : (homMk f).hom = f := sorry

/-- Every ordinary full-subbicategory morphism is recovered by lifting its ambient
representative. -/
@[simp]
theorem homMk_ambient (f : X ⟶ Y) : homMk f.hom = f := sorry

/-- The ordinary forgetful functor from a full subbicategory to its ambient strict bicategory. -/
abbrev forgetFunctor (P : ObjectProperty D) : P.FullSubbicategory ⥤ D :=
  (ObjectProperty.FullSubbicategory.ι P).toFunctor

/-- The two lifted directions of an ambient isomorphism satisfy the first inverse law. -/
theorem homMk_comp_inv (e : X.1 ≅ Y.1) :
    homMk e.hom ≫ homMk e.inv = 𝟙 X := sorry

/-- The two lifted directions of an ambient isomorphism satisfy the second inverse law. -/
theorem inv_comp_homMk (e : X.1 ≅ Y.1) :
    homMk e.inv ≫ homMk e.hom = 𝟙 Y := sorry

/-- Lift an ambient ordinary isomorphism between selected objects to the full subbicategory. -/
def isoMk (e : X.1 ≅ Y.1) : X ≅ Y where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := homMk_comp_inv e
  inv_hom_id := inv_comp_homMk e

/-- Mapping a lifted ordinary isomorphism through the canonical ambient functor recovers its
ambient isomorphism. -/
@[simp]
theorem isoMk.mapIso.hom (e : X.1 ≅ Y.1) :
    ((forgetFunctor P).mapIso (isoMk e)).hom = e.hom := sorry

/-- Mapping the inverse of a lifted ordinary isomorphism through the canonical ambient functor
recovers its ambient inverse. -/
@[simp]
theorem isoMk.mapIso.inv (e : X.1 ≅ Y.1) :
    ((forgetFunctor P).mapIso (isoMk e)).inv = e.inv := sorry

namespace toFullSubcategory

/-- The ordinary full-subcategory object underlying a full-subbicategory object. -/
def obj (X : P.FullSubbicategory) : P.FullSubcategory :=
  ⟨X.1, X.2⟩

/-- Forget a full-subbicategory morphism to the ordinary full subcategory. -/
def map {X Y : P.FullSubbicategory} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ObjectProperty.homMk f.hom

/-- The ordinary forgetful map preserves identities. -/
theorem map_id (X : P.FullSubbicategory) : map (𝟙 X) = 𝟙 (obj X) := sorry

/-- The ordinary forgetful map preserves composition. -/
theorem map_comp {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g := sorry

end toFullSubcategory

/-- View the ordinary category underlying a full subbicategory as the corresponding mathlib
full subcategory. -/
def toFullSubcategory (P : ObjectProperty D) :
    P.FullSubbicategory ⥤ P.FullSubcategory where
  obj := toFullSubcategory.obj
  map := toFullSubcategory.map
  map_id := toFullSubcategory.map_id
  map_comp := toFullSubcategory.map_comp

namespace fromFullSubcategory

/-- The full-subbicategory object corresponding to an ordinary full-subcategory object. -/
def obj (X : P.FullSubcategory) : P.FullSubbicategory :=
  ⟨X.obj, X.property⟩

/-- Lift an ordinary full-subcategory morphism to the full subbicategory. -/
def map {X Y : P.FullSubcategory} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  homMk f.hom

/-- The ordinary lifting map preserves identities. -/
theorem map_id (X : P.FullSubcategory) : map (𝟙 X) = 𝟙 (obj X) := sorry

/-- The ordinary lifting map preserves composition. -/
theorem map_comp {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g := sorry

end fromFullSubcategory

/-- View a mathlib full subcategory inside a strict bicategory as the ordinary category
underlying its full subbicategory. -/
def fromFullSubcategory (P : ObjectProperty D) :
    P.FullSubcategory ⥤ P.FullSubbicategory where
  obj := fromFullSubcategory.obj
  map := fromFullSubcategory.map
  map_id := fromFullSubcategory.map_id
  map_comp := fromFullSubcategory.map_comp

namespace categoryEquivalence

/-- Unit component for the ordinary full-subcategory/full-subbicategory comparison. -/
def unitApp (P : ObjectProperty D) (X : P.FullSubcategory) :
    X ≅ (fromFullSubcategory P ⋙ toFullSubcategory P).obj X :=
  ObjectProperty.isoMk P (Iso.refl X.obj)

/-- Naturality of the ordinary comparison unit. -/
theorem unitApp_naturality (P : ObjectProperty D)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    f ≫ (unitApp P Y).hom =
      (unitApp P X).hom ≫ (fromFullSubcategory P ⋙ toFullSubcategory P).map f := sorry

/-- Unit of the ordinary full-subcategory/full-subbicategory equivalence. -/
def unitIso (P : ObjectProperty D) :
    𝟭 P.FullSubcategory ≅ fromFullSubcategory P ⋙ toFullSubcategory P :=
  NatIso.ofComponents (unitApp P) (fun _ ↦ unitApp_naturality P _)

/-- Counit component for the ordinary full-subcategory/full-subbicategory comparison. -/
def counitApp (P : ObjectProperty D) (X : P.FullSubbicategory) :
    (toFullSubcategory P ⋙ fromFullSubcategory P).obj X ≅ X :=
  isoMk (Iso.refl X.1)

/-- Naturality of the ordinary comparison counit. -/
theorem counitApp_naturality (P : ObjectProperty D)
    {X Y : P.FullSubbicategory} (f : X ⟶ Y) :
    (toFullSubcategory P ⋙ fromFullSubcategory P).map f ≫ (counitApp P Y).hom =
      (counitApp P X).hom ≫ f := sorry

/-- Counit of the ordinary full-subcategory/full-subbicategory equivalence. -/
def counitIso (P : ObjectProperty D) :
    toFullSubcategory P ⋙ fromFullSubcategory P ≅ 𝟭 P.FullSubbicategory :=
  NatIso.ofComponents (counitApp P) (fun _ ↦ counitApp_naturality P _)

/-- Triangle identity for the ordinary full-subcategory/full-subbicategory comparison. -/
theorem functor_unitIso_comp (P : ObjectProperty D) (X : P.FullSubcategory) :
    (fromFullSubcategory P).map ((unitIso P).hom.app X) ≫
      (counitIso P).hom.app ((fromFullSubcategory P).obj X) = 𝟙 _ := sorry

end categoryEquivalence

/-- The mathlib full subcategory of a strict bicategory is equivalent to the ordinary category
underlying its full subbicategory. The object and morphism data are unchanged. -/
def categoryEquivalence (P : ObjectProperty D) :
    P.FullSubcategory ≌ P.FullSubbicategory where
  functor := fromFullSubcategory P
  inverse := toFullSubcategory P
  unitIso := categoryEquivalence.unitIso P
  counitIso := categoryEquivalence.counitIso P
  functor_unitIso_comp := categoryEquivalence.functor_unitIso_comp P

end ObjectProperty.FullSubbicategory

namespace Equivalence

variable {A : Type uA} [Category.{vA} A]
variable {D : Type u} [Bicategory.{w, v} D] [Bicategory.Strict D]

namespace restrictFullSubbicategory

/-- The pointwise correspondence of object properties is the inverse-image equality expected by
`Equivalence.congrFullSubcategory`. -/
theorem inverseImage_eq (e : A ≌ D) {P : ObjectProperty A} {Q : ObjectProperty D}
    (h : ∀ X, P X ↔ Q (e.functor.obj X)) :
    Q.inverseImage e.functor = P := sorry

end restrictFullSubbicategory

/-- Restrict an equivalence of ordinary categories to a source full subcategory and a target
full subbicategory when their object properties correspond under the forward functor.

The construction first uses mathlib's `Equivalence.congrFullSubcategory`, then changes only the
target presentation via `ObjectProperty.FullSubbicategory.categoryEquivalence`. No inverse
functor is selected from a mere essential-surjectivity proposition. -/
def restrictFullSubbicategory (e : A ≌ D) {P : ObjectProperty A} {Q : ObjectProperty D}
    [Q.IsClosedUnderIsomorphisms] (h : ∀ X, P X ↔ Q (e.functor.obj X)) :
    P.FullSubcategory ≌ Q.FullSubbicategory :=
  (e.congrFullSubcategory (restrictFullSubbicategory.inverseImage_eq e h)).trans
    (ObjectProperty.FullSubbicategory.categoryEquivalence Q)

end Equivalence

end CategoryTheory
