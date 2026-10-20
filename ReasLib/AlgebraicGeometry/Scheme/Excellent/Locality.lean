module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.RingTheory.Excellent.Locality

/-!
# Local criteria for (quasi-)excellent schemes

Quasi-excellence and excellence can each be checked on every affine open, on
an affine open cover, or on an open cover, and pass to every open subscheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is quasi-excellent if and only if the section ring of every
affine open is a quasi-excellent ring. -/
@[stacks 0HAB]
theorem quasiExcellent_iff_forall_affineOpen (X : Scheme.{u}) :
    QuasiExcellent X ↔ ∀ U : X.affineOpens, IsQuasiExcellentRing.{u,u} Γ(X, U) :=
  sorry

/-- A scheme is quasi-excellent if and only if some affine open cover has
quasi-excellent section rings. -/
@[stacks 0HAB]
theorem quasiExcellent_iff_exists_affineOpenCover (X : Scheme.{u}) :
    QuasiExcellent X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsQuasiExcellentRing.{u,u} Γ(X, (𝒰.f i).opensRange) :=
  sorry

/-- A scheme is quasi-excellent if and only if some open cover consists of
quasi-excellent open subschemes. -/
@[stacks 0HAB]
theorem quasiExcellent_iff_exists_openCover (X : Scheme.{u}) :
    QuasiExcellent X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, QuasiExcellent ((𝒰.f i).opensRange).toScheme :=
  sorry

/-- Every open subscheme of a quasi-excellent scheme is quasi-excellent. -/
@[stacks 0HAB]
theorem quasiExcellent_toScheme {X : Scheme.{u}} [QuasiExcellent X] (U : X.Opens) :
    QuasiExcellent U.toScheme := sorry

/-- A scheme is excellent if and only if the section ring of every affine
open is an excellent ring. -/
@[stacks 0HAB]
theorem excellent_iff_forall_affineOpen (X : Scheme.{u}) :
    Excellent X ↔ ∀ U : X.affineOpens, IsExcellentRing.{u,u} Γ(X, U) := sorry

/-- A scheme is excellent if and only if some affine open cover has excellent
section rings. -/
@[stacks 0HAB]
theorem excellent_iff_exists_affineOpenCover (X : Scheme.{u}) :
    Excellent X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsExcellentRing.{u,u} Γ(X, (𝒰.f i).opensRange) :=
  sorry

/-- A scheme is excellent if and only if some open cover consists of
excellent open subschemes. -/
@[stacks 0HAB]
theorem excellent_iff_exists_openCover (X : Scheme.{u}) :
    Excellent X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Excellent ((𝒰.f i).opensRange).toScheme :=
  sorry

/-- Every open subscheme of an excellent scheme is excellent. -/
@[stacks 0HAB]
theorem excellent_toScheme {X : Scheme.{u}} [Excellent X] (U : X.Opens) :
    Excellent U.toScheme := sorry

end AlgebraicGeometry.Scheme
