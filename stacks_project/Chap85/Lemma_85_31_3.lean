/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

/-!
# Lemma 85.31.3

A descent datum relative to a quasi-compact flat surjective morphism is effective
when its unique component is locally Artinian.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.DescentData
namespace IsEffective

/-- Lemma 85.31.3: if `f : X ⟶ S` is a quasi-compact, flat, and surjective morphism of
schemes, and `D` is a descent datum relative to `f` whose unique component is locally
Artinian (equivalently, a disjoint union of spectra of Artinian rings), then `D` is
effective. -/
@[stacks 024I]
theorem ofIsLocallyArtinian {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [Flat f] [Surjective f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [IsLocallyArtinian (D.obj default).left] :
    D.IsEffective := sorry

/-- A descent datum relative to a quasi-compact, flat, and surjective morphism is
effective if its unique component is isomorphic to a coproduct of spectra of Artinian
rings. -/
theorem of_sigma_artinianSpec {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [Flat f] [Surjective f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    {I : Type u} (A : I → CommRingCat.{u}) [∀ i, IsArtinianRing (A i)]
    (e : (D.obj default).left ≅ ∐ fun i ↦ Spec (A i)) :
    D.IsEffective := sorry

end IsEffective
end AlgebraicGeometry.Scheme.DescentData
