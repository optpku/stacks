/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.8.3: a scheme is Cohen-Macaulay exactly when the section ring of
every affine open is Cohen-Macaulay. -/
@[stacks 02IQ] #check
  (AlgebraicGeometry.Scheme.cohenMacaulay_iff_forall_affineOpen_sectionsRing_cohenMacaulayRing :
    ∀ X : Scheme.{u},
      Scheme.CohenMacaulay X ↔
        ∀ U : X.affineOpens, CohenMacaulayRing (Γ(X, U)))

variable (X : Scheme.{u})

/- The affine-cover criterion for Cohen-Macaulay schemes. -/
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing
      X (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) :
    Scheme.CohenMacaulay X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, CohenMacaulayRing (Γ(X, (𝒰.f i).opensRange)))

/- The open-cover criterion for Cohen-Macaulay schemes. -/
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally
      X (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) :
    Scheme.CohenMacaulay X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, Scheme.CohenMacaulay ((𝒰.f i).opensRange).toScheme)

/- Cohen-Macaulayness restricts to every open subscheme. -/
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_toScheme :
    ∀ {X : Scheme.{u}},
      Scheme.CohenMacaulay X →
        ∀ U : X.Opens, Scheme.CohenMacaulay U.toScheme)
