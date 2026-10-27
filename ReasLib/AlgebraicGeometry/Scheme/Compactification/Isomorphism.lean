/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior

@[expose] public section

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- An ambient isomorphism preserving both compactification triangles gives an isomorphism
of fixed-interior compactifications. -/
def isoMkOfAmbient {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    P ≅ Q :=
  ObjectProperty.isoMk _ (Under.isoMk (Over.isoMk e hp) (by
    ext
    exact hi))

/-- The forward ambient map of the induced compactification isomorphism is the given map. -/
@[simp]
theorem isoMkOfAmbient_hom {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    ambientMap (isoMkOfAmbient e hi hp).hom = e.hom := rfl

/-- The reverse ambient map of the induced compactification isomorphism is the given inverse. -/
@[simp]
theorem isoMkOfAmbient_inv {S : Scheme.{u}} {X : Over S} {P Q : Of S X}
    (e : P.obj.right.left ≅ Q.obj.right.left)
    (hi : ι P ≫ e.hom = ι Q) (hp : e.hom ≫ Q.obj.right.hom = P.obj.right.hom) :
    ambientMap (isoMkOfAmbient e hi hp).inv = e.inv := rfl

/-- Forget a fixed-interior isomorphism to its actual two ambient maps. -/
def ambientIso {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    P.obj.right.left ≅ Q.obj.right.left where
  hom := ambientMap e.hom
  inv := ambientMap e.inv
  hom_inv_id := congrArg (fun k : P ⟶ P => ambientMap k) e.hom_inv_id
  inv_hom_id := congrArg (fun k : Q ⟶ Q => ambientMap k) e.inv_hom_id

/-- The ambient isomorphism preserves the fixed interior map. -/
theorem ambientIso_interior {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    ι P ≫ (ambientIso e).hom = ι Q :=
  congrArg (fun k => k.left) (Under.w e.hom.hom)

/-- The ambient isomorphism is over the original base. -/
theorem ambientIso_over {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (e : P ≅ Q) :
    (ambientIso e).hom ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w e.hom.hom.right

end AlgebraicGeometry.Scheme.Compactification.Of
end
end
