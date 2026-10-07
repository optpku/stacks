module

public import ReasLib.CategoryTheory.Sites.Point.Construction
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w u' v'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} (p : Point.{w} J)

/-- The cone legs determine the unique morphism from a compatible limiting
element to each object of the category of elements. -/
theorem initialConeHom_unique
    {c : Cone (CategoryOfElements.π p.fiber)}
    (hc : IsLimit c) (x : p.fiber.obj c.pt)
    (hx : ∀ U : p.fiber.Elements,
      p.fiber.map (c.π.app U) x = U.2)
    (U : p.fiber.Elements)
    (m : p.fiber.elementsMk c.pt x ⟶ U) :
    m = CategoryOfElements.homMk (p.fiber.elementsMk c.pt x) U
      (c.π.app U) (hx U) := sorry

/-- A compatible element of a limit cone gives an initial object in the
category of elements. -/
noncomputable def initialOfLimitCone
    {c : Cone (CategoryOfElements.π p.fiber)}
    (hc : IsLimit c) (x : p.fiber.obj c.pt)
    (hx : ∀ U : p.fiber.Elements,
      p.fiber.map (c.π.app U) x = U.2) :
    IsInitial (p.fiber.elementsMk c.pt x) :=
  IsInitial.ofUniqueHom
    (fun U ↦ CategoryOfElements.homMk (p.fiber.elementsMk c.pt x) U
      (c.π.app U) (hx U))
    (fun U m ↦ initialConeHom_unique p hc x hx U m)

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- The naturality equation for evaluation at an initial neighborhood. -/
theorem fromPresheafFiber_naturality
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x))
    {P Q : Cᵒᵖ ⥤ A} (g : P ⟶ Q) :
    p.presheafFiber.map g ≫
        (p.isColimitPresheafFiberCocone Q).desc
          (coconeOfDiagramTerminal h.op ((CategoryOfElements.π p.fiber).op ⋙ Q)) =
      (p.isColimitPresheafFiberCocone P).desc
        (coconeOfDiagramTerminal h.op ((CategoryOfElements.π p.fiber).op ⋙ P)) ≫
        g.app (op X) := sorry

/-- The map from the presheaf fiber to evaluation at an initial neighborhood. -/
noncomputable def fromPresheafFiberNatTrans
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x)) :
    p.presheafFiber (A := A) ⟶ (evaluation Cᵒᵖ A).obj (op X) where
  app P := (p.isColimitPresheafFiberCocone P).desc
    (coconeOfDiagramTerminal h.op ((CategoryOfElements.π p.fiber).op ⋙ P))
  naturality P Q g := fromPresheafFiber_naturality p h g

/-- Evaluation followed by the canonical map back to the fiber is the identity. -/
theorem toPresheafFiber_fromPresheafFiber
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x))
    (P : Cᵒᵖ ⥤ A) :
    (fromPresheafFiberNatTrans p h).app P ≫
        (p.toPresheafFiberNatTrans X x).app P = 𝟙 _ := sorry

/-- The canonical map followed by evaluation at an initial neighborhood is the identity. -/
theorem fromPresheafFiber_toPresheafFiber
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x))
    (P : Cᵒᵖ ⥤ A) :
    (p.toPresheafFiberNatTrans X x).app P ≫
        (fromPresheafFiberNatTrans p h).app P = 𝟙 _ := sorry

/-- The presheaf fiber is naturally isomorphic to evaluation at an initial neighborhood. -/
noncomputable def presheafFiberIsoOfInitial
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x)) :
    p.presheafFiber (A := A) ≅ (evaluation Cᵒᵖ A).obj (op X) where
  hom := fromPresheafFiberNatTrans p h
  inv := p.toPresheafFiberNatTrans X x
  hom_inv_id := NatTrans.ext <| funext fun P ↦
    toPresheafFiber_fromPresheafFiber p h P
  inv_hom_id := NatTrans.ext <| funext fun P ↦
    fromPresheafFiber_toPresheafFiber p h P

/-- The sheaf fiber is naturally isomorphic to evaluation at an initial neighborhood. -/
noncomputable def sheafFiberIsoOfInitial
    {X : C} {x : p.fiber.obj X}
    (h : IsInitial (p.fiber.elementsMk X x)) :
    p.sheafFiber (A := A) ≅
      sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op X) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A)
    (presheafFiberIsoOfInitial p h)

end CategoryTheory.GrothendieckTopology.Point

end
