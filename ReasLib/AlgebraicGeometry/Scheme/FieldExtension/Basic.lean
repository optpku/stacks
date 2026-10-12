/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine

/-!
# Basic field-extension base change of schemes

This leaf owns the canonical `Spec K ⟶ Spec k` morphism associated to a field extension and the
corresponding pullback of a scheme over `k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Pullback

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension

/-- The canonical morphism `Spec K ⟶ Spec k` induced by the field extension `k ⟶ K`. -/
abbrev specMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Scheme.AffineBaseChange.specMap k K

/-- The base change of `f : X ⟶ Spec k` along the field extension `Spec K ⟶ Spec k`. -/
abbrev baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  Scheme.AffineBaseChange.baseChange k K f

/-- The projection from the field-extension base change back to `X`. -/
abbrev toSource
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    FieldExtension.baseChange k K f ⟶ X :=
  Scheme.AffineBaseChange.toSource k K f

/-- The projection from the field-extension base change to `Spec K`. -/
abbrev toBase
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    FieldExtension.baseChange k K f ⟶ Spec (CommRingCat.of K) :=
  Scheme.AffineBaseChange.toBase k K f

end FieldExtension

namespace Scheme.Modules

namespace FieldExtension

/-- The pullback of a scheme module to a field-extension base change. -/
abbrev baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (L : X.Modules) :
    (FieldExtension.baseChange k K f).Modules :=
  Scheme.Modules.AffineBaseChange.baseChange k K f L

end FieldExtension

end Scheme.Modules

end AlgebraicGeometry
