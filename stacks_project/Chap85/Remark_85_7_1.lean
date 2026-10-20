/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.RingedMorphism
import StacksCheckRecall

/-!
# Remark 85.7.1

A morphism of ringed simplicial sites in Situation 85.3.3 is a pair
`(h, hSharp)` where `h` is a morphism of simplicial sites as in Remark 85.5.1
and `hSharp` is a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O`, equivalently `O' ⟶ h_total,* O`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]

/- Remark 85.7.1 (1)
A simplicial morphism and its inverse-image ring homomorphism form a ringed morphism. -/
@[stacks 0DGZ] #check (CategoryTheory.SimplicialSites.RingedMorphism.ofHom :
    ∀ (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P]
    (hSharp : (IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O),
    RingedMorphism J J' O O')

/- Inverse-image and direct-image ring homomorphisms correspond under the canonical adjunction. -/
#check (CategoryTheory.SimplicialSites.RingedMorphism.structureMapEquiv :
    ∀ (h : C' ⟶ C) [IsMorphism J J' h]
    [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, (IsMorphism.totalFunctor h).op.HasLeftKanExtension P],
    ((IsMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (IsMorphism.total J J' h).ringDirectImage.obj O))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- Remark 85.7.1 (2)
A simplicial morphism and its inverse-image ring homomorphism form a ringed morphism. -/
@[stacks 0DGZ] #check (CategoryTheory.Grothendieck.RingedMorphism.ofHom :
    ∀ (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P]
    (hSharp : (IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O),
    RingedMorphism J J' O O')

/- Inverse-image and direct-image ring homomorphisms correspond under the canonical adjunction. -/
#check (CategoryTheory.Grothendieck.RingedMorphism.structureMapEquiv :
    ∀ (h : F ⟶ F') [IsFiberwiseMorphism J J' h]
    [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
      (Grothendieck.map h).op.HasPointwiseRightKanExtension P],
    ((IsFiberwiseMorphism.total J J' h).ringInverseImage.obj O' ⟶ O) ≃
      (O' ⟶ (IsFiberwiseMorphism.total J J' h).ringDirectImage.obj O))

end CategoryTheory.Grothendieck
