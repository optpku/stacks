/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Stalk

/-!
# Stalks of the sheaf cotangent complex

Lemma 92.18.9 identifies the stalk of `L(φ)` at a site point `p` with the
algebra cotangent complex of the stalk map `A_p ⟶ B_p`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open HomologicalComplex
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] [LocallySmall.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J)

/- Lemma 92.18.9. The stalk of the cotangent complex of a morphism of ring sheaves
is canonically the cotangent complex of the induced stalk homomorphism. -/
@[stacks 08T0] #check (SheafOfModules.RingedSite.CotangentComplex.Stalk.iso :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J),
    (p.moduleStalkComplex B).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)) ≅
      CategoryTheory.CommRingCat.Under.CotangentComplex.obj
        (p.stalkCommRing A) (Under.mk (p.stalkCommRingMap φ)))

#check (SheafOfModules.RingedSite.CotangentComplex.Stalk.iso_hom_f :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (p : Point.{u} J) (n : ℕ),
    (Stalk.iso φ p).hom.f (-n) =
      (Stalk.sourceXIso φ p n).hom ≫
        (Stalk.termIso φ p n).hom ≫ (Stalk.targetXIso φ p n).inv)

end
end
