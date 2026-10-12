/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative differentials and sheafification

This file compares sheafification of the sectionwise Kähler-differential
presheaf with the relative-differentials sheaf formed after sheafifying the
two commutative-ring presheaves.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials.Sheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The morphism of commutative-ring sheaves obtained by sheafifying a
morphism of commutative-ring presheaves. -/
abbrev ringMap (phi : O₁ ⟶ O₂) :
    PresheafOfModules.commRingSheafification J O₁ ⟶
      PresheafOfModules.commRingSheafification J O₂ :=
  PresheafOfModules.commRingSheafificationMap J phi

/-- The module sheaf obtained by sheafifying the sectionwise relative
differentials of a presheaf morphism. -/
abbrev ofPresheaf (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J
      (PresheafOfModules.commRingSheafification J O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj
    (relativeDifferentials' phi)

/-- The relative-differentials sheaf formed after sheafifying the two ring
presheaves. -/
abbrev afterSheafification (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J
      (PresheafOfModules.commRingSheafification J O₂) :=
  relativeDifferentials (ringMap J phi)

/-- The presheaf morphism defining the comparison under the
module-sheafification adjunction. -/
noncomputable def unitMap (phi : O₁ ⟶ O₂) :
    relativeDifferentials' phi ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap J O₂)).obj
          (relativeDifferentials' (ringMap J phi).hom) :=
  PresheafOfModules.RelativeDifferentials.map
    (PresheafOfModules.commRingSheafificationSquare J phi)

/-- The canonical comparison from sheafified sectionwise differentials to
the differentials of the sheafified ring map. -/
noncomputable def comparison (phi : O₁ ⟶ O₂) :
    ofPresheaf J phi ⟶ afterSheafification J phi :=
  (PresheafOfModules.sheafificationHomEquiv
      (PresheafOfModules.sheafificationRingMap J O₂)).symm
    (unitMap J phi ≫
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.sheafificationRingMap J O₂)).map
          (moduleSheafificationUnitToVal
            (PresheafOfModules.commRingSheafification J O₂)
            (relativeDifferentials' (ringMap J phi).hom)))

/-- Lemma 18.33.4 (08TP): the comparison between the two
relative-differentials sheafifications is an isomorphism. -/
@[stacks 08TP]
instance comparison_isIso (phi : O₁ ⟶ O₂) :
    IsIso (comparison J phi) := sorry

end SheafOfModules.RingedSite.RelativeDifferentials.Sheafification
