module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.RingTheory.Normal.Nagata.Locality

@[expose] public section

/-!
# Affine locality of universally Japanese and Nagata schemes

These are specialized views of the generic
`Scheme.HasRingPropertyLocally` locality API.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

namespace UniversallyJapanese

/-- A scheme is universally Japanese exactly when every affine open has a
universally Japanese section ring. -/
@[stacks 033W]
theorem iff_forall_affineOpen :
    UniversallyJapanese X ↔
      ∀ U : X.affineOpens, UniversallyJapaneseRing.{u, u} (Γ(X, U)) := sorry

/-- A scheme is universally Japanese exactly when some affine open cover has
universally Japanese section rings. -/
@[stacks 033W]
theorem iff_exists_affineOpenCover :
    UniversallyJapanese X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, UniversallyJapaneseRing.{u, u} (Γ(X, (𝒰.f i).opensRange)) := sorry

end UniversallyJapanese

/-- A scheme is universally Japanese exactly when some open cover consists of
universally Japanese schemes. -/
@[stacks 033W]
theorem universallyJapanese_iff_exists_openCover_by_universallyJapanese :
    UniversallyJapanese X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, UniversallyJapanese ((𝒰.f i).opensRange).toScheme := sorry

/-- Every open subscheme of a universally Japanese scheme is universally
Japanese. -/
@[stacks 033W]
theorem universallyJapanese_toScheme (hX : UniversallyJapanese X) (U : X.Opens) :
    UniversallyJapanese U.toScheme := sorry

/-- A scheme is Nagata exactly when every affine open has a Nagata section
ring. -/
@[stacks 033X]
theorem nagata_iff_forall_affineOpen_sectionsRing_nagataRing :
    Nagata X ↔
      ∀ U : X.affineOpens, NagataRing (Γ(X, U)) := sorry

/-- A scheme is Nagata exactly when some affine open cover has Nagata section
rings. -/
@[stacks 033X]
theorem nagata_iff_exists_affineOpenCover_sectionsRing_nagataRing :
    Nagata X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, NagataRing (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- A scheme is Nagata exactly when some open cover consists of Nagata
schemes. -/
@[stacks 033X]
theorem nagata_iff_exists_openCover_by_nagata :
    Nagata X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Nagata ((𝒰.f i).opensRange).toScheme := sorry

/-- Every open subscheme of a Nagata scheme is Nagata. -/
@[stacks 033X]
theorem nagata_toScheme {X : Scheme.{u}} (hX : Nagata X) (U : X.Opens) :
    Nagata U.toScheme := sorry

end AlgebraicGeometry.Scheme
