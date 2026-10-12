/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Monic
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.OfIso
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Map
public import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of monic truncated splittings

This module transports monicity and splitness along isomorphisms and functors. Ordinary proof
terms form the reusable API; instances are thin wrappers for typeclass search.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v₂ u₂

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace Splitting

variable {n : ℕ} {X : SimplicialObject.Truncated C n} {s : Splitting X}

namespace IsMonic

/-- Transport an explicit proof of monicity along an isomorphism of truncated simplicial
objects. -/
@[stacks 017P "monicity after transporting a truncated splitting"]
theorem ofIso (hs : s.IsMonic) {Y : SimplicialObject.Truncated C n} (e : X ≅ Y) :
    (s.ofIso e).IsMonic := sorry

/-- A functor preserving monomorphisms sends an explicitly monic truncated splitting to a monic
splitting. -/
@[stacks 017P "monicity of the functorial image of a truncated splitting"]
theorem map (hs : s.IsMonic) {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] [F.PreservesMonomorphisms] :
    (s.map F).IsMonic := sorry

end IsMonic

namespace ofIso

/-- Typeclass transport of monicity along an isomorphism of truncated simplicial objects. -/
@[stacks 017P "monicity instance after transporting a truncated splitting"]
instance isMonic {Y : SimplicialObject.Truncated C n} (e : X ≅ Y) [s.IsMonic] :
    (s.ofIso e).IsMonic := sorry

end ofIso

namespace map

/-- Typeclass transport of monicity through a functor preserving finite coproducts and
monomorphisms. -/
@[stacks 017P "monicity instance for the functorial image of a truncated splitting"]
instance isMonic {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] [F.PreservesMonomorphisms] [s.IsMonic] :
    (s.map F).IsMonic := sorry

end map

end Splitting

namespace IsSplit

/-- Splitness of a truncated simplicial object is preserved along an isomorphism. -/
@[stacks 017P "transport of split truncated simplicial objects along isomorphisms"]
theorem ofIso {n : ℕ} {X Y : SimplicialObject.Truncated C n} (e : X ≅ Y) :
    IsSplit X → IsSplit Y := sorry

/-- Splitness is invariant under isomorphism of truncated simplicial objects. -/
@[stacks 017P "isomorphism invariance of split truncated simplicial objects"]
theorem iff_of_iso {n : ℕ} {X Y : SimplicialObject.Truncated C n} (e : X ≅ Y) :
    IsSplit X ↔ IsSplit Y := sorry

/-- A functor preserving finite coproducts and monomorphisms preserves split truncated
simplicial objects. -/
@[stacks 017P "functorial preservation of split truncated simplicial objects"]
theorem map {n : ℕ} {X : SimplicialObject.Truncated C n}
    (hX : IsSplit X) {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] [F.PreservesMonomorphisms] :
    IsSplit (X ⋙ F) := sorry

end IsSplit

end CategoryTheory.SimplicialObject.Truncated
