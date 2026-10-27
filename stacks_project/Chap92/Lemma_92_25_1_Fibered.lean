/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Fibered

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

/-- Source notation for the canonical category of polynomial affine diagrams. -/
abbrev Obj (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] := category Λ X

/- Lemma 92.25.1: restriction of a polynomial affine diagram gives a strongly
cartesian lift, and the projection to the small Zariski site is fibered. -/
#check (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski_isFibered :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    (AlgebraicGeometry.Scheme.CotangentSite.forgetZariski Λ X).IsFibered)

#check (AlgebraicGeometry.Scheme.CotangentSite.restrictHom_isStronglyCartesian :
  ∀ {Λ : CommRingCat.{u}} {X : Scheme.{u}} [X.Over (Spec Λ)]
    (P : category Λ X) {U : X.smallZariskiSite}
    (f : U ⟶ (forgetZariski Λ X).obj P),
    (forgetZariski Λ X).IsStronglyCartesian f (restrictHom P f))

end AlgebraicGeometry.Scheme.CotangentSite
