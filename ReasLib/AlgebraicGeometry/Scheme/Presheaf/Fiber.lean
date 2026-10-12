/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Fibers of transformations of presheaves on schemes over a base
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- The structure morphism of a scheme over `T`, viewed as a morphism in `Over S`. -/
def fromOver {S : Scheme.{u}} {T : Over S} (T' : Over T.left) :
    (Over.map T.hom).obj T' ⟶ T :=
  Over.homMk T'.hom

/-- The underlying scheme morphism of `fromOver T'` is the structure map of `T'`. -/
theorem fromOver_left {S : Scheme.{u}} {T : Over S} (T' : Over T.left) :
    (fromOver T').left = T'.hom := sorry

/-- Restriction of a section `y : G.obj (op T)` along a scheme `T'` over `T`. -/
def restrictSection {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type v}
    {T : Over S} (y : G.obj (op T)) (T' : Over T.left) :
    G.obj (op ((Over.map T.hom).obj T')) :=
  G.map (op (fromOver T')) y

/-- Restriction of a section is the image of that section under `G.map` of `fromOver`. -/
theorem restrictSection_eq {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type v}
    {T : Over S} (y : G.obj (op T)) (T' : Over T.left) :
    restrictSection y T' = G.map (op (fromOver T')) y := sorry

/-- The fiber of a transformation `a : F ⟶ G` over a section `y : G.obj (op T)`, as a
subfunctor of the restriction of `F` to schemes over `T`. -/
def fiber {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T : Over S} (y : G.obj (op T)) :
    Subfunctor ((Over.map T.hom).op ⋙ F) where
  obj T' :=
    { x | a.app (op ((Over.map T.hom).obj T'.unop)) x = restrictSection y T'.unop }
  map := sorry

/-- Membership in the fiber over `y` is the equalizer condition `a(x) = y` restricted to `T'`. -/
theorem mem_fiber_obj {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T : Over S} (y : G.obj (op T)) {T' : (Over T.left)ᵒᵖ}
    {x : ((Over.map T.hom).op ⋙ F).obj T'} :
    x ∈ (fiber a y).obj T' ↔
      a.app (op ((Over.map T.hom).obj T'.unop)) x = restrictSection y T'.unop := sorry

/-- The fiber functor of a transformation `a : F ⟶ G` over `y : G.obj (op T)`. -/
def fiberFunctor {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T : Over S} (y : G.obj (op T)) : (Over T.left)ᵒᵖ ⥤ Type v :=
  (fiber a y).toFunctor

/-- The value of the fiber functor is the subtype of sections of `F` mapping to the
restriction of `y`. -/
theorem fiberFunctor_obj {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T : Over S} (y : G.obj (op T)) (T' : (Over T.left)ᵒᵖ) :
    (fiberFunctor a y).obj T' = (fiber a y).obj T' := sorry

end AlgebraicGeometry.Scheme.Over
