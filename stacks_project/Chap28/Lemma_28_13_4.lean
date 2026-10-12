/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Japanese
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 28.13.4

The nonempty affine-open and open-cover criteria for integral Japanese schemes
live in `ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Japanese`.
-/

universe u

/- Lemma 28.13.4: An integral scheme is Japanese precisely when its nonempty
affine opens have Japanese section rings. -/
@[stacks 033V]
#check (AlgebraicGeometry.Scheme.isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
    AlgebraicGeometry.Scheme.IsJapanese X ↔
      ∀ U : X.affineOpens,
        ∀ hU : Nonempty U,
          AlgebraicGeometry.Scheme.affineOpenSectionsIsN2Ring X U hU)

#check (AlgebraicGeometry.Scheme.isJapanese_iff_exists_affineOpenCover_sectionsRing_isN2Ring :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
    AlgebraicGeometry.Scheme.IsJapanese X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ∀ hU : Nonempty (𝒰.f i).opensRange,
            AlgebraicGeometry.Scheme.affineOpenSectionsIsN2Ring X
              ⟨(𝒰.f i).opensRange,
                AlgebraicGeometry.isAffineOpen_opensRange (𝒰.f i)⟩ hU)

#check (AlgebraicGeometry.Scheme.isJapanese_iff_exists_openCover_by_isJapanese :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
    AlgebraicGeometry.Scheme.IsJapanese X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀,
          ∀ [Nonempty (𝒰.f i).opensRange],
            AlgebraicGeometry.Scheme.IsJapanese ((𝒰.f i).opensRange).toScheme)

#check (AlgebraicGeometry.Scheme.isJapanese_toScheme :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X],
    AlgebraicGeometry.Scheme.IsJapanese X →
      ∀ (U : X.Opens) [Nonempty U],
        AlgebraicGeometry.Scheme.IsJapanese U.toScheme)
