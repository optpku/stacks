/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Descent and cancellation for quasi-finiteness

This module keeps the morphism-theoretic descent facts separate from affine-open computation and
from the basic global quasi-finite owner.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes that is locally of finite type and a monomorphism is locally
quasi-finite. -/
@[stacks 0CT8]
theorem locallyQuasiFinite_of_locallyOfFiniteType_of_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Mono f] :
    LocallyQuasiFinite f := sorry

/-- If a composite of scheme morphisms is quasi-finite at a point of its source, then its left
factor is quasi-finite at that point. -/
theorem quasiFiniteAt_of_comp_quasiFiniteAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hfg : (f ≫ g).QuasiFiniteAt x) :
    f.QuasiFiniteAt x := sorry

/-- Finite-type quasi-finiteness at a point descends from a composite to its left factor. -/
@[stacks 03WR]
theorem Scheme.Hom.FiniteType.QuasiFiniteAt.of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hfg : Scheme.Hom.FiniteType.QuasiFiniteAt (f ≫ g) x) :
    Scheme.Hom.FiniteType.QuasiFiniteAt f x := sorry

/-- Local finite type together with local quasi-finiteness descends from a composite to its left
factor. -/
@[stacks 03WR]
theorem Scheme.Hom.FiniteType.locallyQuasiFinite_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hfg : LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g)) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f := sorry

/-- If `f` is surjective, `f ≫ g` is locally quasi-finite, and `g` is locally of finite type, then
`g` is locally quasi-finite. -/
@[stacks 0GWS]
theorem locallyQuasiFinite_of_surjective_of_comp_locallyQuasiFinite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [LocallyQuasiFinite (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyQuasiFinite g := sorry

end AlgebraicGeometry
