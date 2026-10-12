/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over

/-!
# Concrete views of finite-presentation over-categories

This leaf exposes the underlying `Over` objects and morphisms obtained from
base change or restriction in `FinitePresentationOver`. These views avoid
repeated unwrapping of full-subcategory inclusions in downstream statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FinitePresentationOver

/-- The concrete `Over` object obtained by base changing a finite-presentation object. -/
abbrev baseChangeOverObject {T T' : Scheme.{u}} (f : T' ⟶ T)
    (X : FinitePresentationOver T) : Over T' :=
  (Over.pullback f).obj X.obj

/-- The concrete `Over` morphism obtained by base changing a morphism between
finite-presentation objects. -/
abbrev baseChangeOverHom {T T' : Scheme.{u}} (f : T' ⟶ T)
    {X Y : FinitePresentationOver T} (a : X ⟶ Y) :
    baseChangeOverObject f X ⟶ baseChangeOverObject f Y :=
  (Over.pullback f).map ((inclusion T).map a)

/-- Restrict a finite-presentation object over an open subscheme to a smaller open, retaining
only the concrete `Over` object. -/
abbrev restrictOverObject {S : Scheme.{u}} {W U' : S.Opens}
    (hWU' : W ≤ U') (X : FinitePresentationOver U'.toScheme) : Over W.toScheme :=
  baseChangeOverObject (S.homOfLE hWU') X

/-- Restrict a morphism between finite-presentation objects over an open subscheme to a smaller
open, retaining only the concrete `Over` morphism. -/
abbrev restrictOverHom {S : Scheme.{u}} {W U' : S.Opens}
    (hWU' : W ≤ U') {X Y : FinitePresentationOver U'.toScheme} (a : X ⟶ Y) :
    restrictOverObject hWU' X ⟶ restrictOverObject hWU' Y :=
  baseChangeOverHom (S.homOfLE hWU') a

/-- The underlying morphism of schemes associated to a morphism in a finite-presentation
over-category. -/
abbrev underlyingHom {T : Scheme.{u}} {X Y : FinitePresentationOver T} (a : X ⟶ Y) :
    X.obj.left ⟶ Y.obj.left :=
  ((inclusion T).map a).left

end FinitePresentationOver

end AlgebraicGeometry
