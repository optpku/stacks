/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.RingTheory.Regular.Local
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable (X : Scheme.{u})

/- Lemma 28.9.3 (1): a scheme is regular if and only if the section ring of every affine open is
Noetherian and regular, as expressed by `IsRegularRing`. -/
@[stacks 02IU] #check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
      (fun A : CommRingCat.{u} ↦ IsRegularRing A) :
    AlgebraicGeometry.Scheme.Regular X ↔
      ∀ U : X.affineOpens, IsRegularRing (Γ(X, (U : X.Opens))))

/- Lemma 28.9.3 (2): a scheme is regular if and only if it has an affine open cover whose section
rings are Noetherian and regular, as expressed by `IsRegularRing`. -/
@[stacks 02IU]
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
      (fun A : CommRingCat.{u} ↦ IsRegularRing A) :
    AlgebraicGeometry.Scheme.Regular X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsRegularRing (Γ(X, (𝒰.openCover.f i).opensRange)))

/- Lemma 28.9.3 (3): a scheme is regular if and only if it has an open cover whose associated
open subschemes are regular. -/
@[stacks 02IU]
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
      (fun A : CommRingCat.{u} ↦ IsRegularRing A) :
    AlgebraicGeometry.Scheme.Regular X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, AlgebraicGeometry.Scheme.Regular ((𝒰.f i).opensRange).toScheme)

/- Lemma 28.9.3 (4): every open subscheme of a regular scheme is regular. -/
@[stacks 02IU]
#check
  (AlgebraicGeometry.Scheme.hasRingPropertyLocally_toScheme
      (X := X) (P := fun A : CommRingCat.{u} ↦ IsRegularRing A) :
    AlgebraicGeometry.Scheme.Regular X →
      ∀ U : X.Opens, AlgebraicGeometry.Scheme.Regular U.toScheme)
