module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections.Grading
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# The morphism to the projective spectrum of a section ring

An invertible module whose positive homogeneous nonvanishing opens cover a scheme determines a
canonical morphism to the projective spectrum of its tensor-power section ring.  The comparison
with integral twists is represented as a morphism of graded algebra sheaves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open Scheme.Modules
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The section ring of an invertible scheme module has its canonical commutative-ring
structure. -/
noncomputable instance instCommRingSectionRing
    (L : X.Modules) [hL : Invertible L] :
    CommRing (RingedSpace.GradedSections.ring L) :=
  @DirectSum.commRing ℕ _ (RingedSpace.GradedSections.degree L) _ _
    (@RingedSpace.GradedSections.instGCommRing _ L
      (Invertible.ringedSpaceIsInvertible hL))

/-- The internal homogeneous summands give the section ring of an invertible scheme module its
canonical grading. -/
noncomputable instance instGradedRingSectionRing
    (L : X.Modules) [hL : Invertible L] :
    GradedRing (RingedSpace.GradedSections.grading L) :=
  @DirectSum.InternalGrading.instGradedRing ℕ _ _
    (RingedSpace.GradedSections.degree L) _
    (@RingedSpace.GradedSections.instGCommRing _ L
      (Invertible.ringedSpaceIsInvertible hL)).toGRing

/-- Positive-degree tensor-power sections have nonvanishing opens covering the scheme. -/
def IsSectionRingCover (L : X.Modules) [hL : Invertible L] : Prop :=
  ∀ x : X, ∃ n : ℕ, 0 < n ∧
    ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤), x ∈ hL.nonvanishingOpen s

/-- A multiplicative comparison from the pullback of a projective twist presentation to the
integral tensor powers of an invertible module. -/
structure SectionRingProjComparison
    (L : X.Modules) [hL : Invertible L]
    (P : ProjTwistPresentation (RingedSpace.GradedSections.grading L))
    (f : X ⟶ Proj (RingedSpace.GradedSections.grading L)) where
  /-- The comparison as a homomorphism of integral graded algebra sheaves. -/
  hom : P.twistAlgebra.pullbackAlgebra f ⟶
    @RingedSpace.InvertiblePower.gradedAlgebra _ L
      (Invertible.ringedSpaceIsInvertible hL)

namespace SectionRingProjComparison

variable {L : X.Modules} [hL : Invertible L]
variable {P : ProjTwistPresentation (RingedSpace.GradedSections.grading L)}
variable {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}

/-- Build a comparison from a homomorphism between the coherent graded algebra models. -/
def of
    (hom : P.twistAlgebra.pullbackAlgebra f ⟶
      @RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Invertible.ringedSpaceIsInvertible hL)) :
    SectionRingProjComparison L P f where
  hom := hom

/-- The actual degree-`n` comparison from the pulled-back projective twist to the integral power. -/
def component (c : SectionRingProjComparison L P f) (n : ℤ) :
    (pullback f).obj (P.actualTwist n) ⟶
      @RingedSpace.InvertiblePower.sheaf _ L
        (Invertible.ringedSpaceIsInvertible hL) n :=
  (P.twistAlgebra.pullbackIso f n).hom ≫ c.hom.hom n

/-- The actual degree-zero comparison preserves the canonical unit section. -/
theorem component_map_one (c : SectionRingProjComparison L P f) (U : (X.Opens)ᵒᵖ) :
    (((c.component 0).val.app U).hom) (P.actualOne f U) =
      @RingedSpace.InvertiblePower.oneSection _ L
        (Invertible.ringedSpaceIsInvertible hL) U := sorry

/-- The actual degreewise comparison preserves multiplication of local twist sections. -/
theorem component_map_mul (c : SectionRingProjComparison L P f) (U : (X.Opens)ᵒᵖ)
    (a b : ℤ) (x : projTwistPullbackSection P.actualTwist f a U)
    (y : projTwistPullbackSection P.actualTwist f b U) :
    (((c.component (a + b)).val.app U).hom) (P.actualMul f U a b x y) =
      @RingedSpace.InvertiblePower.mulSection _ L
        (Invertible.ringedSpaceIsInvertible hL) U a b
        ((((c.component a).val.app U).hom) x)
        ((((c.component b).val.app U).hom) y) := sorry

/-- A comparison is canonical when it recovers every nonnegative homogeneous section and is
locally an isomorphism in all degrees after one positive rescaling. -/
def IsCanonical (c : SectionRingProjComparison L P f) : Prop :=
  (∀ (n : ℕ) (s : RingedSpace.GradedSections.grading L n),
    ((P.actualSectionMap n ≫ globalSectionsPullback f (P.actualTwist (n : ℤ)) ≫
        globalSectionsMap (c.component (n : ℤ))).hom) s =
      (((@RingedSpace.InvertiblePower.natIso _ L
        (Invertible.ringedSpaceIsInvertible hL) n).hom.val.app (op ⊤)).hom)
        ((DirectSum.InternalGrading.summandEquiv
          (RingedSpace.GradedSections.degree L) n).symm s)) ∧
  ∀ x : X, ∃ d : ℕ, 0 < d ∧ ∃ U : X.Opens, x ∈ U ∧
    ∀ n : ℤ, IsIso ((restrictFunctor U.ι).map (c.component ((d : ℤ) * n)))

/-- Canonicity is equivalent to section identity in nonnegative degrees and the rescaled local
isomorphism property in every integer degree. -/
theorem isCanonical_iff (c : SectionRingProjComparison L P f) :
    c.IsCanonical ↔
      ((∀ (n : ℕ) (s : RingedSpace.GradedSections.grading L n),
        ((P.actualSectionMap n ≫ globalSectionsPullback f (P.actualTwist (n : ℤ)) ≫
            globalSectionsMap (c.component (n : ℤ))).hom) s =
          (((@RingedSpace.InvertiblePower.natIso _ L
            (Invertible.ringedSpaceIsInvertible hL) n).hom.val.app (op ⊤)).hom)
            ((DirectSum.InternalGrading.summandEquiv
              (RingedSpace.GradedSections.degree L) n).symm s)) ∧
      ∀ x : X, ∃ d : ℕ, 0 < d ∧ ∃ U : X.Opens, x ∈ U ∧
        ∀ n : ℤ, IsIso ((restrictFunctor U.ι).map (c.component ((d : ℤ) * n)))) := sorry

namespace IsCanonical

/-- A canonical comparison induces the identity on every nonnegative homogeneous section. -/
theorem section_identity {c : SectionRingProjComparison L P f} (hc : c.IsCanonical)
    (n : ℕ) (s : RingedSpace.GradedSections.grading L n) :
    ((P.actualSectionMap n ≫ globalSectionsPullback f (P.actualTwist (n : ℤ)) ≫
        globalSectionsMap (c.component (n : ℤ))).hom) s =
      (((@RingedSpace.InvertiblePower.natIso _ L
        (Invertible.ringedSpaceIsInvertible hL) n).hom.val.app (op ⊤)).hom)
        ((DirectSum.InternalGrading.summandEquiv
          (RingedSpace.GradedSections.degree L) n).symm s) := sorry

/-- Around every point, a positive rescaling makes all comparison components isomorphisms. -/
theorem locally_isIso {c : SectionRingProjComparison L P f} (hc : c.IsCanonical) (x : X) :
    ∃ d : ℕ, 0 < d ∧ ∃ U : X.Opens, x ∈ U ∧
      ∀ n : ℤ, IsIso ((restrictFunctor U.ι).map (c.component ((d : ℤ) * n))) := sorry

end IsCanonical

end SectionRingProjComparison

/-- A morphism to the projective spectrum of the section ring has the expected basic-open
preimages and a canonical comparison for every explicit twist presentation. -/
def IsSectionRingProjMap (L : X.Modules) [hL : Invertible L]
    (f : X ⟶ Proj (RingedSpace.GradedSections.grading L)) : Prop :=
  (∀ (n : ℕ) (hn : 0 < n) (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)),
    f ⁻¹ᵁ Proj.basicOpen (RingedSpace.GradedSections.grading L)
        (DirectSum.InternalGrading.summandEquiv
          (RingedSpace.GradedSections.degree L) n s) =
      hL.nonvanishingOpen s) ∧
  ∀ P : ProjTwistPresentation (RingedSpace.GradedSections.grading L),
    ∃ c : SectionRingProjComparison L P f, c.IsCanonical

/-- The section-ring projective-map predicate is characterized by its basic-open formula and
canonical twist comparison. -/
theorem isSectionRingProjMap_iff (L : X.Modules) [hL : Invertible L]
    (f : X ⟶ Proj (RingedSpace.GradedSections.grading L)) :
    IsSectionRingProjMap L f ↔
      ((∀ (n : ℕ) (hn : 0 < n) (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)),
        f ⁻¹ᵁ Proj.basicOpen (RingedSpace.GradedSections.grading L)
            (DirectSum.InternalGrading.summandEquiv
              (RingedSpace.GradedSections.degree L) n s) =
          hL.nonvanishingOpen s) ∧
      ∀ P : ProjTwistPresentation (RingedSpace.GradedSections.grading L),
        ∃ c : SectionRingProjComparison L P f, c.IsCanonical) := sorry

namespace IsSectionRingProjMap

/-- The preimage of a positive homogeneous basic open is its section nonvanishing open. -/
theorem preimage_basicOpen {L : X.Modules} [hL : Invertible L]
    {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}
    (hf : IsSectionRingProjMap L f) (n : ℕ) (hn : 0 < n)
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) :
    f ⁻¹ᵁ Proj.basicOpen (RingedSpace.GradedSections.grading L)
        (DirectSum.InternalGrading.summandEquiv
          (RingedSpace.GradedSections.degree L) n s) =
      hL.nonvanishingOpen s := sorry

/-- Every explicit twist presentation admits a canonical comparison along the map. -/
theorem comparison_exists {L : X.Modules} [Invertible L]
    {f : X ⟶ Proj (RingedSpace.GradedSections.grading L)}
    (hf : IsSectionRingProjMap L f)
    (P : ProjTwistPresentation (RingedSpace.GradedSections.grading L)) :
    ∃ c : SectionRingProjComparison L P f, c.IsCanonical := sorry

end IsSectionRingProjMap

/-- If positive homogeneous nonvanishing opens cover a scheme, there is a morphism to the
projective spectrum of the tensor-power section ring with the canonical comparison properties. -/
theorem exists_sectionRingProj (L : X.Modules) [Invertible L]
    (h_cover : IsSectionRingCover L) :
    ∃ f : X ⟶ Proj (RingedSpace.GradedSections.grading L), IsSectionRingProjMap L f := sorry

end AlgebraicGeometry.Scheme.Modules
