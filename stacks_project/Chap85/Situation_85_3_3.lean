module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos
public import ReasLib.CategoryTheory.Sites.Simplicial.MorphismDiagram
import StacksCheckRecall

/-!
# Situation 85.3.3

Working setup with two alternative presentations of a simplicial diagram of
sites: morphisms of sites (case A) or cocontinuous functors with property `P`
(case B), together with the named morphisms of topoi `f_φ` and the total site.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

/- Situation 85.3.3 (1): case A, a covariant simplex diagram of morphisms of sites.
For `φ : m ⟶ n` the continuous functor `u_φ : C.obj m ⥤ C.obj n` presents a
morphism of sites `f_φ : C.obj n ⟶ C.obj m` and a morphism of topoi
`f_φ : Sh(C.obj n) ⟶ Sh(C.obj m)`; `C_total` is the total site of Lemma 85.3.1. -/
@[stacks 09WE] #check (CategoryTheory.SimplicialSites.toposMap :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      (C.map φ).toFunctor.op.HasLeftKanExtension P]
    [CategoryTheory.SimplicialSites.IsMorphismDiagram C J]
    {m n : SimplexCategory} (φ : m ⟶ n),
      MorphismOfTopoiIn.{u, u, v, v, w} (J m).toGrothendieck (J n).toGrothendieck)

#check (CategoryTheory.SimplicialSites.IsMorphismDiagram :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      (C.map φ).toFunctor.op.HasLeftKanExtension P], Prop)

#check (CategoryTheory.SimplicialSites.totalSite :
  (C : SimplexCategory ⥤ Cat.{v, u}) → Type u)

#check (CategoryTheory.SimplicialSites.precoverage :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)),
    Precoverage (CategoryTheory.SimplicialSites.totalSite C))

#check (CategoryTheory.SimplicialSites.topology :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)),
    GrothendieckTopology (CategoryTheory.SimplicialSites.totalSite C))

/- Situation 85.3.3 (2): case B, a simplicial object of sites whose structure maps
are cocontinuous functors with property `P`. For `φ : m ⟶ n` the functor
`u_φ : C_n ⥤ C_m` induces `f_φ : Sh(C_n) ⟶ Sh(C_m)`; `C_total` is the total site
of Lemma 85.3.2. -/
@[stacks 09WE] #check (CategoryTheory.Grothendieck.toposMap :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    [CategoryTheory.Grothendieck.IsFiberwiseSite F J]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      (F.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P]
    {m n : SimplexCategory} (φ : m ⟶ n),
      MorphismOfTopoiIn.{u, u, v, v, w}
        (J (op m)).toGrothendieck (J (op n)).toGrothendieck)

#check (CategoryTheory.Grothendieck.IsFiberwiseSite :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n)), Prop)

#check (CategoryTheory.Grothendieck :
  (F : SimplicialObject Cat.{v, u}) → Type u)

#check (CategoryTheory.Grothendieck.precoverage :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n)),
    Precoverage (CategoryTheory.Grothendieck F))

#check (CategoryTheory.Grothendieck.topology :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n)),
    GrothendieckTopology (CategoryTheory.Grothendieck F))
