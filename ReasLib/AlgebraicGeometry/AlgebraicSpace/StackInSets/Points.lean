module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor

/-!
# Scheme-valued points as fibre objects

A morphism from a scheme to an algebraic space determines an object of its stack of points
in the fibre over that scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Convert a morphism `T → X` of algebraic spaces over `S` into the corresponding object of
the stack in sets `𝒮_X` over `T`, via the category-of-elements encoding of `stackInSets`. -/
def objOfHom {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ X) :
    (stackInSets X).p.Fiber T :=
  Functor.Fiber.mk
    (a := (op ⟨op T, yonedaEquiv (f : yoneda.obj T ⟶ X.functorOfPoints)⟩ :
      (stackInSets X).total))
    rfl

/-- The functor-of-points value stored by `objOfHom f` is the Yoneda transpose of `f`. -/
theorem objOfHom_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (f : ofOver T ⟶ X) :
    yonedaEquiv (f : yoneda.obj T ⟶ X.functorOfPoints) = (objOfHom f).1.unop.snd :=
  rfl

namespace stackInSets

/-- The scheme over the ambient base underlying a scheme-valued point. -/
abbrev pointBase {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : Over S :=
  x.unop.fst.unop

/-- The underlying scheme is the first component of the category-of-elements object. -/
theorem pointBase_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : pointBase x = x.unop.fst.unop := rfl

/-- The morphism of algebraic spaces represented by a scheme-valued point. -/
def pointHom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : ofOver (pointBase x) ⟶ T :=
  yonedaEquiv.symm x.unop.snd

/-- The point morphism is the Yoneda transpose of its section. -/
theorem pointHom_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) :
    pointHom x = yonedaEquiv.symm x.unop.snd := rfl

/-- The scheme morphism underlying a morphism of scheme-valued points. -/
def pointMap {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : (stackInSets T).total} (f : x ⟶ y) : pointBase x ⟶ pointBase y :=
  f.unop.val.unop

/-- The scheme morphism is the opposite of the category-of-elements map. -/
theorem pointMap_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : (stackInSets T).total} (f : x ⟶ y) :
    pointMap f = f.unop.val.unop := rfl

/-- Morphisms of scheme-valued points commute with their morphisms to the algebraic space. -/
theorem pointHom_naturality {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : (stackInSets T).total} (f : x ⟶ y) :
    (ofOverFunctor S).map (pointMap f) ≫ pointHom y = pointHom x := sorry

end stackInSets

end AlgebraicGeometry.AlgebraicSpace
