/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Compatibility checks for the promoted nonconstancy declarations. -/
#check (AlgebraicGeometry.Scheme.Hom.IsNonconstant :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.isNonconstant_iff_not_isConstant :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    f.IsNonconstant ↔ ¬ ∀ x y : X, f x = f y)

#check (AlgebraicGeometry.Scheme.Hom.IsNonconstant.isDominant_of_curves :
  ∀ {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [Curve X] [Curve Y] {f : X ⟶ Y} (hf : f.left.IsNonconstant),
    IsDominant f.left)

end AlgebraicGeometry.Scheme.Hom
