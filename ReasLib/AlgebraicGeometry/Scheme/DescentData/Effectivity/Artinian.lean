module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

/-!
# Effectivity of Artinian scheme descent data

A descent datum along a quasi-compact flat surjective morphism is effective when
the scheme in its single covering-family component is locally Artinian.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.DescentData
namespace IsEffective

/-- A descent datum along a quasi-compact flat surjective morphism is effective
if the scheme in its single covering-family component is locally Artinian. -/
theorem ofIsLocallyArtinian {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [Flat f] [Surjective f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    [IsLocallyArtinian (D.obj default).left] :
    D.IsEffective := sorry

/-- A descent datum along a quasi-compact flat surjective morphism is effective
if the scheme in its single covering-family component is isomorphic to a coproduct
of spectra of Artinian rings. -/
theorem of_sigma_artinianSpec {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [Flat f] [Surjective f]
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
    {I : Type u} (A : I → CommRingCat.{u}) [∀ i, IsArtinianRing (A i)]
    (e : (D.obj default).left ≅ ∐ fun i ↦ Spec (A i)) :
    D.IsEffective := sorry

end IsEffective
end AlgebraicGeometry.Scheme.DescentData
