/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-!
# Automorphism functors of families of curves

The group algebraic space `Aut_S(X)` of a family of curves is the isomorphism
presheaf of the family with itself, reindexed to schemes over the base of the
family. Representability is a proposition, not a chosen algebraic-space
witness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The family `P` as an object of the fibre of `p S` over its base scheme. -/
def asFiber {S : Scheme.{u}} (P : Obj S) : (p S).Fiber (base P) :=
  ⟨P, rfl⟩

/-- The underlying family of `asFiber P` is `P`. -/
theorem asFiber_obj {S : Scheme.{u}} (P : Obj S) : (asFiber P).val = P :=
  rfl

/-- `asFiber P` lies over the base scheme of `P`. -/
theorem asFiber_eq {S : Scheme.{u}} (P : Obj S) :
    (p S).obj (asFiber P).val = base P :=
  rfl

/-- The functor of points `T ↦ Aut_T(X_T)` of a family of curves, as the
isomorphism presheaf of the family with itself, reindexed along the iterated
slice equivalence to schemes over the base. Hom-types of `Obj S` live in
`Type (u + 1)`. -/
def autFunctor {S : Scheme.{u}} (P : Obj S) :
    (Over (base P).left)ᵒᵖ ⥤ Type (u + 1) :=
  (base P).iteratedSliceEquiv.inverse.op ⋙
    Functor.isomorphismPresheaf (p S) (asFiber P) (asFiber P)

/-- `autFunctor P` is precomposition of the fibrewise isomorphism presheaf with
the opposite of the iterated-slice inverse. -/
theorem autFunctor_obj {S : Scheme.{u}} (P : Obj S) :
    autFunctor P =
      (base P).iteratedSliceEquiv.inverse.op ⋙
        Functor.isomorphismPresheaf (p S) (asFiber P) (asFiber P) :=
  rfl

/-- An algebraic space over the base of `P` represents `autFunctor P` after
universe lift of its functor of points. -/
def IsRepresentedBy {S : Scheme.{u}} (P : Obj S)
    (G : AlgebraicSpace (base P).left) : Prop :=
  Nonempty (autFunctor P ≅ G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Representability of `autFunctor P` by `G` means the functors of points are
isomorphic after universe lift. -/
theorem IsRepresentedBy_iff {S : Scheme.{u}} (P : Obj S)
    (G : AlgebraicSpace (base P).left) :
    IsRepresentedBy P G ↔
      Nonempty (autFunctor P ≅ G.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  Iff.rfl

/-- The automorphism algebraic space of a family of curves is unramified over
its base: every representing algebraic space has unramified structure
morphism. -/
def IsUnramified {S : Scheme.{u}} (P : Obj S) : Prop :=
  ∀ (G : AlgebraicSpace (base P).left),
    IsRepresentedBy P G → AlgebraicSpace.Unramified (SchemeRealization.toBase G)

/-- Unramifiedness of `Aut_S(X)` means every representing algebraic space is
unramified over the base. -/
theorem isUnramified_iff {S : Scheme.{u}} (P : Obj S) :
    IsUnramified P ↔
      ∀ (G : AlgebraicSpace (base P).left),
        IsRepresentedBy P G →
          AlgebraicSpace.Unramified (SchemeRealization.toBase G) :=
  Iff.rfl

/-- The automorphism functor of a family of curves is representable by an
algebraic space over the base. -/
theorem autFunctor_isRepresentable {S : Scheme.{u}} (P : Obj S) :
    ∃ G : AlgebraicSpace (base P).left, IsRepresentedBy P G :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
