module

public import ReasLib.CategoryTheory.Sites.Simplicial.Morphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialMorphism

/-!
# Morphisms of simplicial sites

The two component predicates describe morphisms in the covariant and
fiberwise presentations of simplicial sites.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

section

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [SimplicialSites.IsMorphismDiagram C J] [SimplicialSites.IsMorphismDiagram C' J']

#check (CategoryTheory.SimplicialSites.IsMorphism J J' : (C' ⟶ C) → Prop)

end

section

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [Grothendieck.IsFiberwiseSite F J] [Grothendieck.IsFiberwiseSite F' J']

#check (CategoryTheory.Grothendieck.IsFiberwiseMorphism J J' : (F ⟶ F') → Prop)

end
