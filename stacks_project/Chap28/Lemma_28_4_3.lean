module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 28.4.3

The reusable affine-locality API is owned by
`ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality`.  This chapter
file remains a compatibility entry point for the textbook label.
-/

/- Lemma 28.4.3: an isomorphism-invariant local property of rings holds
locally on a scheme exactly when it holds on every affine open. -/
@[stacks 01OR]
#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing :
  ∀ (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P],
    X.HasRingPropertyLocally P ↔ ∀ U : X.affineOpens, P (Γ(X, U)))

#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing :
  ∀ (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P],
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, P (Γ(X, (𝒰.f i).opensRange)))

#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally :
  ∀ (X : Scheme.{u}) (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P],
    X.HasRingPropertyLocally P ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.HasRingPropertyLocally P)

#check (AlgebraicGeometry.Scheme.instHasRingPropertyLocallyToScheme :
  ∀ {X : Scheme.{u}} {P : CommRingCat.{u} → Prop} [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P]
    [X.HasRingPropertyLocally P] (U : X.Opens),
    U.toScheme.HasRingPropertyLocally P)

#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_toScheme :
  ∀ {X : Scheme.{u}} {P : CommRingCat.{u} → Prop} [RingPropertyIsLocal P]
    [CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms P],
    X.HasRingPropertyLocally P → ∀ U : X.Opens, U.toScheme.HasRingPropertyLocally P)
