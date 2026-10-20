/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise monic ideal actions on homological complexes

This file lifts monicity of an ideal-sheaf action from module sheaves to arbitrary homological
complexes.  The owner is independent of chain/cochain orientation and of the index type.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace SheafOfModules.RingedSite.IdealSheaf.IsActionMono

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable {ι : Type z}

/-- The object property of homological complexes on which the ideal-sheaf action is monic in
every degree. -/
@[stacks 0F8N "degreewise monic ideal action"]
def complex (I : Subobject (unitModule J O)) (c : ComplexShape ι) :
    ObjectProperty
      (HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c) :=
  HomologicalComplex.termsIn c
    (SheafOfModules.RingedSite.IdealSheaf.IsActionMono I)

/-- A homological complex has monic `I`-action when it belongs to the canonical termwise
object property.  This class is the typeclass-facing view of `complex`. -/
@[stacks 0F8N "degreewise ideal-action predicate"]
class Complex
    (I : Subobject (unitModule J O)) {c : ComplexShape ι}
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c) : Prop where
  /-- The underlying membership in the termwise object property. -/
  mem : complex I c K

/-- Homological complexes with degreewise monic `I`-action, as a full subcategory. -/
abbrev Complexes
    (I : Subobject (unitModule J O)) (c : ComplexShape ι) :=
  (complex I c).FullSubcategory

/-- Membership in `IsActionMono.complex I c` is equivalent to monicity in every degree. -/
theorem complex_iff
    (I : Subobject (unitModule J O)) {c : ComplexShape ι}
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c) :
    complex I c K ↔ ∀ i : ι,
      SheafOfModules.RingedSite.IdealSheaf.IsActionMono I (K.X i) := sorry

/-- The object-property and typeclass views of degreewise monic ideal action agree. -/
theorem complex_iff_complex
    (I : Subobject (unitModule J O)) {c : ComplexShape ι}
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c) :
    complex I c K ↔ Complex I K := sorry

/-- Every term of a complex with degreewise monic ideal action inherits the corresponding
module-level instance. -/
instance Complex.term
    (I : Subobject (unitModule J O)) {c : ComplexShape ι}
    (K : HomologicalComplex (ringedSiteModuleCategory.{u, v, w, w} J O) c)
    [hK : Complex I K] (i : ι) :
    SheafOfModules.RingedSite.IdealSheaf.IsActionMono I (K.X i) :=
  (complex_iff I K).mp hK.mem i

/-- An object of the full subcategory of degreewise action-monic complexes carries the
corresponding canonical class instance. -/
instance Complexes.complex
    (I : Subobject (unitModule J O)) {c : ComplexShape ι}
    (K : Complexes I c) : Complex I K.obj :=
  ⟨K.property⟩

end SheafOfModules.RingedSite.IdealSheaf.IsActionMono
