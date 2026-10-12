/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.RingTheory.LocalProperty

@[expose] public section

/-!
# Locality criteria for affine-local ring properties

For an isomorphism-invariant property of commutative rings that is local for
principal-open covers, this file relates locality on a scheme to affine charts
and open covers, and records preservation under restriction to open subschemes.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]
  [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P]

/-- A scheme has an affine-local ring property exactly when the section ring
of every affine open has that property. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing :
    X.HasRingPropertyLocally P ↔
      ∀ U : X.affineOpens, P (Γ(X, U)) := sorry

variable {X : Scheme.{u}} {P : CommRingCat.{u} → Prop}

/-- An isomorphism-invariant affine-local ring property restricts to every open
subscheme. -/
instance instHasRingPropertyLocallyToScheme [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P]
    [X.HasRingPropertyLocally P] (U : X.Opens) :
    U.toScheme.HasRingPropertyLocally P := sorry

/-- If an isomorphism-invariant affine-local ring property holds locally on a
scheme, then it holds locally on every open subscheme. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_toScheme [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P]
    (hX : X.HasRingPropertyLocally P) (U : X.Opens) :
    U.toScheme.HasRingPropertyLocally P := sorry

variable (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]
  [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P]

/-- A scheme has an affine-local ring property exactly when some affine open
cover has section rings with that property. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing :
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, P (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- A scheme has an affine-local ring property exactly when some open cover
consists of open subschemes on which the property holds locally. -/
@[stacks 01OR]
theorem hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally :
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.HasRingPropertyLocally P := sorry

end AlgebraicGeometry.Scheme
