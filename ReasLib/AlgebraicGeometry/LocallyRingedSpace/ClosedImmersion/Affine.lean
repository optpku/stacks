/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Locality
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.AffineKernel
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine models of closed immersions

Closed immersions into affine schemes are classified using the canonical
kernel ideal on global sections. The same API applies after restriction to
an affine chart of an arbitrary target scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

namespace AffineQuotient

/-- The map from the coordinate ring of an affine target to the global
sections of the source. -/
@[stacks 01IN "global-sections map of an affine closed subspace"]
def sectionsMap
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    CommRingCat.of R ⟶ LocallyRingedSpace.Γ.obj (Opposite.op Z) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ LocallyRingedSpace.Γ.map i.op

/-- The spectrum of the quotient by the global-sections kernel ideal. -/
@[stacks 01IN "canonical affine quotient spectrum"]
abbrev spec
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) : Scheme.{u} :=
  Spec (CommRingCat.of (R ⧸ i.globalSectionsKernelIdeal))

/-- The map from the quotient coordinate ring to the global sections of the
source, induced by the universal property of the quotient by a kernel. -/
@[stacks 01IN "affine quotient-to-sections map"]
def quotientToSections
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    CommRingCat.of (R ⧸ i.globalSectionsKernelIdeal) ⟶
      LocallyRingedSpace.Γ.obj (Opposite.op Z) :=
  CommRingCat.ofHom (sectionsMap i).hom.kerLift

/-- The canonical inclusion of the affine quotient into the original affine
target. -/
@[stacks 01IN "canonical affine quotient inclusion"]
def ι
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    (spec i).toLocallyRingedSpace ⟶
      (Spec (CommRingCat.of R)).toLocallyRingedSpace :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk i.globalSectionsKernelIdeal))).toLRSHom

/-- The canonical comparison from a locally ringed space over `Spec R` to the
spectrum of the quotient by its global-sections kernel. -/
@[stacks 01IN "canonical affine quotient comparison"]
def comparison
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    Z ⟶ (spec i).toLocallyRingedSpace :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv Z
    (Opposite.op (CommRingCat.of (R ⧸ i.globalSectionsKernelIdeal)))
    (quotientToSections i).op

/-- The canonical affine quotient comparison followed by the quotient
inclusion is the original morphism. -/
@[stacks 01IN "canonical affine quotient factorization", reassoc]
theorem comparison_ι
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    comparison i ≫ ι i = i := sorry

/-- A morphism to the canonical affine quotient lying over `Spec R` is the canonical
comparison. -/
@[stacks 01IN "canonical affine quotient uniqueness"]
theorem comparison_unique
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace)
    (f : Z ⟶ (spec i).toLocallyRingedSpace) (hf : f ≫ ι i = i) :
    f = comparison i := sorry

/-- For a closed immersion into an affine scheme, the canonical affine quotient comparison is
an open immersion. -/
@[stacks 01IN "canonical affine quotient open immersion"]
instance comparison_isOpenImmersion
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace)
    [IsClosedImmersion i] : IsOpenImmersion (comparison i) := sorry

/-- The canonical affine quotient comparison of a closed immersion is surjective on points. -/
@[stacks 01IN "canonical affine quotient surjectivity"]
theorem comparison_surjective
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace)
    [IsClosedImmersion i] :
    Function.Surjective (comparison i).base := sorry

/-- The canonical affine quotient comparison of a closed immersion into an affine scheme is an
isomorphism. -/
@[stacks 01IN "canonical affine quotient comparison is invertible"]
theorem comparison_isIso
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace)
    [IsClosedImmersion i] : IsIso (comparison i) := sorry

/-- The kernel ideal sheaf of a closed immersion into an affine spectrum is the tilde sheaf of
its global-sections kernel ideal. -/
@[stacks 01IN "kernel ideal sheaf of an affine closed immersion"]
theorem kernelSheafIsomorphicTilde
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) [IsClosedImmersion i] :
    IsIsomorphic (Hom.kernelIdealSheaf i)
      (tilde (ModuleCat.of R i.globalSectionsKernelIdeal) :
        (Spec (CommRingCat.of R)).Modules) := sorry

/-- Any affine quotient presentation of a closed immersion uses its canonical kernel ideal. -/
@[stacks 01IH "uniqueness of the affine quotient ideal"]
theorem ideal_eq_of_isIsomorphic
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) [IsClosedImmersion i]
    (I : Ideal R)
    (hI : IsIsomorphic (Over.mk i)
      (Over.mk ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom))) :
    I = i.globalSectionsKernelIdeal := sorry

/-- Closed immersions into an affine scheme are classified by a unique ideal. -/
@[stacks 01IH "classification by the global-sections kernel ideal"]
theorem existsUniqueIdeal
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) [IsClosedImmersion i] :
    ∃! I : Ideal R,
      IsIsomorphic (Over.mk i)
        (Over.mk ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom)) := sorry

end AffineQuotient

namespace AffineChart

/-- The canonical restriction of a morphism to a chosen affine chart, followed by the chart
identification with an affine spectrum. -/
@[stacks 01IN "canonical morphism over an affine chart"]
noncomputable abbrev restrictedMap
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) {R : Type u} [CommRing R]
    (U : Opens X) (eU : X.restrict U.isOpenEmbedding ≅
      (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    Z.restrict (i.preimageOpen U).isOpenEmbedding ⟶
      (Spec (CommRingCat.of R)).toLocallyRingedSpace :=
  i.restrictToPreimageOpen U ≫ eU.hom

/-- The canonical restriction of a closed immersion to an affine chart, followed by the chart
identification, is again a closed immersion. -/
@[stacks 01IN "canonical affine-chart restriction is closed"]
noncomputable instance restrictedMap_isClosedImmersion
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {R : Type u} [CommRing R] (U : Opens X)
    (eU : X.restrict U.isOpenEmbedding ≅
      (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    IsClosedImmersion (restrictedMap i U eU) := sorry

end AffineChart

namespace AffineOpen

/-- The canonical locally-ringed-space identification of an affine open with the spectrum of its
section ring. -/
@[stacks 01IN "affine-open target identification"]
noncomputable abbrev targetIso {X : Scheme.{u}} (U : X.affineOpens) :
    X.toLocallyRingedSpace.restrict U.1.isOpenEmbedding ≅
      (Spec (CommRingCat.of Γ(X, U))).toLocallyRingedSpace :=
  Scheme.forgetToLocallyRingedSpace.mapIso U.2.isoSpec

/-- The canonical restriction to an affine open, viewed as a morphism to the spectrum of its
section ring. -/
@[stacks 01IN "canonical morphism over an affine open"]
noncomputable abbrev restrictedMap
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace) (U : X.affineOpens) :
    Z.restrict (i.preimageOpen U.1).isOpenEmbedding ⟶
      (Spec (CommRingCat.of Γ(X, U))).toLocallyRingedSpace :=
  AffineChart.restrictedMap i U.1 (targetIso U)

/-- The global-sections kernel of the canonical affine-open restriction is the intrinsic kernel
ideal on that target open. -/
@[stacks 01IN "canonical affine-open kernel comparison"]
theorem globalSectionsKernelIdeal_eq
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace) (U : X.affineOpens) :
    (restrictedMap i U).globalSectionsKernelIdeal = affineOpenKernelIdeal i U := sorry

/-- On an affine open, the canonical restriction of a closed immersion is the quotient by its
intrinsic affine-open kernel ideal. -/
@[stacks 01IN "closed immersion over an affine open"]
theorem isIsomorphicQuotient
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] (U : X.affineOpens) :
    IsIsomorphic (Over.mk (restrictedMap i U))
      (Over.mk (Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (affineOpenKernelIdeal i U)))))) := sorry

/-- On an affine open, the kernel ideal sheaf of the canonical restriction is the tilde sheaf
of its intrinsic affine-open kernel ideal. -/
@[stacks 01IN "kernel ideal sheaf over an affine open"]
theorem kernelSheafIsomorphicTilde
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] (U : X.affineOpens) :
    IsIsomorphic (Hom.kernelIdealSheaf (restrictedMap i U))
      (tilde (ModuleCat.of Γ(X, U) (affineOpenKernelIdeal i U)) :
        (Spec (CommRingCat.of Γ(X, U))).Modules) := sorry

end AffineOpen

end AlgebraicGeometry.LocallyRingedSpace.Hom
