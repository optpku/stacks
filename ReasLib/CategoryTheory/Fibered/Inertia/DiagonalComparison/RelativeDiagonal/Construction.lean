module

public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative diagonal construction

This module owns the explicit relative diagonal of a based functor. Object and
morphism projection formulas are provided by `Computations`.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {S' : Type uS'} [Category.{vS'} S']
variable (F : S ⥤ S')
variable (p : S ⥤ C)
variable {p}
variable (p' : S' ⥤ C)

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace RelativeInertia.Implementation

/-- The source object used by the relative diagonal lies in the fiber over its own image. -/
private theorem Diagonal.fiberObject_eq (comm : F ⋙ p' = p) (X : S) :
    p.obj X = p.obj X := sorry
/- Proof strategy: reflexivity. -/

/-- The identity comparison for the relative diagonal lies over the base identity. -/
private theorem Diagonal.fiberHom_isHomLift (comm : F ⋙ p' = p) (X : S) :
    p'.IsHomLift (𝟙 (p.obj X)) (𝟙 (F.obj X)) := sorry
/- Proof strategy: eliminate `comm` and use the canonical identity `IsHomLift` instance for the
based functor `BasedFunctor.ofFunctor F comm`. -/

/-- The identity-shaped morphism in the target fiber used by the relative diagonal. -/
private def Diagonal.fiberHom (comm : F ⋙ p' = p) (X : S) :
    ((BasedFunctor.ofFunctor F comm).fiberFunctor (p.obj X)).obj
        (Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)) ⟶
      ((BasedFunctor.ofFunctor F comm).fiberFunctor (p.obj X)).obj
        (Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)) :=
  ⟨𝟙 (F.obj X), Diagonal.fiberHom_isHomLift F p' comm X⟩

/-- The identity-shaped diagonal fiber morphism is self-inverse. -/
private theorem Diagonal.fiberHom_self_comp (comm : F ⋙ p' = p) (X : S) :
    Diagonal.fiberHom F p' comm X ≫ Diagonal.fiberHom F p' comm X =
      𝟙 _ := sorry
/- Proof strategy: apply `Functor.Fiber.hom_ext` and simplify identities. -/

/-- The identity-shaped comparison isomorphism used by the relative diagonal. -/
private def Diagonal.objIso (comm : F ⋙ p' = p) (X : S) :
    ((BasedFunctor.ofFunctor F comm).fiberFunctor (p.obj X)).obj
        (Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)) ≅
      ((BasedFunctor.ofFunctor F comm).fiberFunctor (p.obj X)).obj
        (Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)) where
  hom := Diagonal.fiberHom F p' comm X
  inv := Diagonal.fiberHom F p' comm X
  hom_inv_id := Diagonal.fiberHom_self_comp F p' comm X
  inv_hom_id := Diagonal.fiberHom_self_comp F p' comm X

/-- The two identical legs of the relative diagonal form a commuting comparison square. -/
private theorem Diagonal.map_comm (comm : F ⋙ p' = p) {X Y : S} (f : X ⟶ Y) :
    CommSq (F.map f) (Diagonal.objIso F p' comm X).hom.1
      (Diagonal.objIso F p' comm Y).hom.1 (F.map f) := sorry
/- Proof strategy: both comparison components are identities, so simplify the square. -/

/-- Object map of the explicit relative diagonal. -/
private def Diagonal.obj (comm : F ⋙ p' = p) (X : S) :
    (PseudoPullback (BasedFunctor.ofFunctor F comm) (BasedFunctor.ofFunctor F comm)).obj :=
  PseudoPullback.mk (BasedFunctor.ofFunctor F comm) (BasedFunctor.ofFunctor F comm) (p.obj X)
    { fst := Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)
      snd := Functor.Fiber.mk (Diagonal.fiberObject_eq F p' comm X)
      iso := Diagonal.objIso F p' comm X }

/-- Each source arrow lies over its image under the source projection. -/
private theorem Diagonal.map_isHomLift (comm : F ⋙ p' = p)
    {X Y : S} (f : X ⟶ Y) : p.IsHomLift (p.map f) f := sorry
/- Proof strategy: use the canonical `Functor.IsHomLift.map` instance. -/

/-- Morphism map of the explicit relative diagonal. -/
private def Diagonal.map (comm : F ⋙ p' = p) {X Y : S} (f : X ⟶ Y) :
    Diagonal.obj F p' comm X ⟶ Diagonal.obj F p' comm Y :=
  PseudoPullback.Hom.mk (p.map f) f (Diagonal.map_isHomLift F p' comm f)
    f (Diagonal.map_isHomLift F p' comm f)
    (Diagonal.map_comm F p' comm f)

/-- The explicit relative diagonal preserves identities. -/
private theorem Diagonal.map_id (comm : F ⋙ p' = p) (X : S) :
    Diagonal.map F p' comm (𝟙 X) =
      𝟙 (Diagonal.obj F p' comm X) := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; both component equalities are identities. -/

/-- The explicit relative diagonal preserves composition. -/
private theorem Diagonal.map_comp (comm : F ⋙ p' = p)
    {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Diagonal.map F p' comm (f ≫ g) =
      Diagonal.map F p' comm f ≫ Diagonal.map F p' comm g := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; both components reduce to composition in `S`. -/

/-- The underlying functor of the explicit relative diagonal. -/
private def Diagonal.functor (comm : F ⋙ p' = p) :
    S ⥤ (PseudoPullback (BasedFunctor.ofFunctor F comm) (BasedFunctor.ofFunctor F comm)).obj where
  obj := Diagonal.obj F p' comm
  map := Diagonal.map F p' comm
  map_id := Diagonal.map_id F p' comm
  map_comp := Diagonal.map_comp F p' comm

/-- The explicit relative diagonal commutes strictly with projection to `C`. -/
private theorem Diagonal.functor_comm (comm : F ⋙ p' = p) :
    Diagonal.functor F p' comm ⋙
      (PseudoPullback (BasedFunctor.ofFunctor F comm) (BasedFunctor.ofFunctor F comm)).p = p := sorry
/- Proof strategy: apply functor extensionality; the stored base object and base map are exactly
`p.obj X` and `p.map f`. -/

/-- Bare-functor implementation of the relative diagonal; use
`BasedFunctor.relativeDiagonal` on bundled input. -/
private def Diagonal.toBasedFunctor (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor p ⥤ᵇ
      PseudoPullback (BasedFunctor.ofFunctor F comm) (BasedFunctor.ofFunctor F comm) where
  toFunctor := Diagonal.functor F p' comm
  w := Diagonal.functor_comm F p' comm

end RelativeInertia.Implementation
end

namespace BasedFunctor

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Functor.Fiber

variable {X Y : BasedCategory C}

/-- The relative diagonal of `F : X ⥤ᵇ Y`. It is induced by the identity-legged square

```
            𝟙 X
 X ─────────────────────────▶ X
 │                            │
𝟙 X│                            │ F
 ▼                            ▼
 X ─────────────────────────▶ Y
             F
```

and therefore has codomain the explicit self-pseudo-pullback `X ×_Y X`. -/
@[stacks 034H "relative diagonal"]
def relativeDiagonal (F : X ⥤ᵇ Y) : X ⥤ᵇ PseudoPullback F F :=
  RelativeInertia.Implementation.Diagonal.toBasedFunctor F.toFunctor Y.p F.w

end BasedFunctor

end CategoryTheory
