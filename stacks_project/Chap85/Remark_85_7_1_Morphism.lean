/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.RingedMorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_6_1_Ringed
public import stacks_project.Chap85.Remark_85_5_1_Morphism

/-!
# Morphisms of ringed simplicial sites (case A)

A morphism of ringed simplicial sites in Situation 85.3.3 case A is a pair
`(h, hSharp)`: an unringed morphism of simplicial sites `α : C' ⟶ C` as in
`IsMorphism`, together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O` along the totalization of `α`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

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

namespace RingedMorphism

variable {J J' O O'}

variable (f : RingedMorphism J J' O O')

/- Remark 85.7.1
Canonical shared mathematical interface. -/
#check (CategoryTheory.SimplicialSites.RingedMorphism.toToposHom f :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology C J) O) (RingedSite.ofRingSheaf (topology C' J') O'))

#check (CategoryTheory.SimplicialSites.RingedMorphism.toToposHom_toTopos f :
    (toToposHom f).toTopos = f.totalTopos)

#check (CategoryTheory.SimplicialSites.RingedMorphism.toToposHom_structureMap f :
    (toToposHom f).structureMap = f.structureMap)

variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.SimplicialSites.modulePullback_underlyingIso C J O :
    ∀ (n : SimplexCategory) (M : SheafOfModules.{w} O),
    (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n)).obj
        ((stageMorphism C J O n).modulePullback.obj M) ≅
      ((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))

end RingedMorphism

end CategoryTheory.SimplicialSites
