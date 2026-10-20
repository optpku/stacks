module

public import ReasLib.CategoryTheory.Sites.Simplicial.RingedMorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_6_1_Fiber
public import stacks_project.Chap85.Remark_85_5_1_Morphism

/-!
# Morphisms of ringed simplicial sites (case B)

A morphism of ringed simplicial sites in Situation 85.3.3 case B is a pair
`(h, hSharp)`: an unringed fiberwise morphism of simplicial sites `α : F ⟶ F'`
as in `IsFiberwiseMorphism`, together with a homomorphism of sheaves of rings
`h_total⁻¹ O' ⟶ O` along the totalization of `α`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

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

namespace RingedMorphism

variable {J J' O O'}

variable (f : RingedMorphism J J' O O')

/- Remark 85.7.1
Canonical shared mathematical interface. -/
#check (CategoryTheory.Grothendieck.RingedMorphism.toToposHom f :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology F J) O) (RingedSite.ofRingSheaf (topology F' J') O'))

#check (CategoryTheory.Grothendieck.RingedMorphism.toToposHom_toTopos f :
    (toToposHom f).toTopos = f.totalTopos)

#check (CategoryTheory.Grothendieck.RingedMorphism.toToposHom_structureMap f :
    (toToposHom f).structureMap = f.structureMap)

variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, (J n).toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Grothendieck.fiberModulePullback_underlyingIso F J O :
    ∀ (n : SimplexCategory) (M : SheafOfModules.{w} O),
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) ≅
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))

end RingedMorphism

end CategoryTheory.Grothendieck
