/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOpenSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Morphisms to projective spectra from graded section maps

A grading-preserving homomorphism from a Veronese ring to the tensor-power section ring of an
invertible module determines a morphism to the corresponding positive-degree open of a projective
spectrum.  Compatibility is expressed using coherent comparisons of twists with tensor powers.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

namespace Proj.DegreeOpenFactorization

/-- A graded section map is compatible with a degree-open factorization and a line-bundle
isomorphism when a coherent twist comparison induces the given map in every degree. -/
def SectionMapCompatible (P : ProjTwistPresentation 𝒜)
    (x : Proj.DegreeOpenFactorization 𝒜 Y) (ℒ : Y.Modules)
    (ψ : GradedRing.Veronese 𝒜 x.degree →+* RingedSpace.GradedSections.ring ℒ)
    (α : lineBundle 𝒜 P x ≅ ℒ) : Prop :=
  ∃ comparison : TwistComparison 𝒜 P x,
    ∀ n (a : GradedRing.Veronese.degree 𝒜 x.degree n),
      (AddCommGrpCat.Hom.hom
          (psiDegreeMap 𝒜 P x comparison n ≫
            Scheme.Modules.globalSectionsMap (RingedSpace.TensorPower.mapIso α n).hom)) a =
        (ψ (DirectSum.of (GradedRing.Veronese.degree 𝒜 x.degree) n a)) n

/-- Compatibility with a degree-open factorization is equivalent to the existence of a coherent
twist comparison whose transported degree maps agree with the given graded map. -/
theorem sectionMapCompatible_iff (P : ProjTwistPresentation 𝒜)
    (x : Proj.DegreeOpenFactorization 𝒜 Y) (ℒ : Y.Modules)
    (ψ : GradedRing.Veronese 𝒜 x.degree →+* RingedSpace.GradedSections.ring ℒ)
    (α : lineBundle 𝒜 P x ≅ ℒ) :
    SectionMapCompatible 𝒜 P x ℒ ψ α ↔
      ∃ comparison : TwistComparison 𝒜 P x,
        ∀ n (a : GradedRing.Veronese.degree 𝒜 x.degree n),
          (AddCommGrpCat.Hom.hom
              (psiDegreeMap 𝒜 P x comparison n ≫
                Scheme.Modules.globalSectionsMap (RingedSpace.TensorPower.mapIso α n).hom)) a =
            (ψ (DirectSum.of (GradedRing.Veronese.degree 𝒜 x.degree) n a)) n := sorry

end Proj.DegreeOpenFactorization

/-- A homomorphism from a Veronese ring to a tensor-power section ring preserves degree when a
homogeneous input has zero component in every different degree. -/
def veroneseSectionMapPreservesDegree (d : ℕ) (ℒ : Y.Modules)
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ) : Prop :=
  ∀ n (a : GradedRing.Veronese.degree 𝒜 d n) ⦃m : ℕ⦄, m ≠ n →
    (ψ (DirectSum.of (GradedRing.Veronese.degree 𝒜 d) n a)) m = 0

/-- The degree-one image of a Veronese section map, regarded as a family of global sections of
the underlying invertible module. -/
noncomputable def veroneseDegreeOneSectionFamily (d : ℕ) (ℒ : Y.Modules)
    [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ) :
    𝒜 d → ℒ.sections :=
  fun a ↦
    SheafOfModules.sectionsMap (RingedSpace.TensorPower.oneIso ℒ).hom
      (RingedSpace.sectionFromTop (RingedSpace.TensorPower.sheaf ℒ 1)
        ((ψ (DirectSum.of (GradedRing.Veronese.degree 𝒜 d) 1
          (Eq.mp (congrArg (fun i : ℕ ↦ ↥(𝒜 i)) (Nat.one_mul d).symm) a))) 1))

/-- The degree-one image of a Veronese section map generates the invertible module. -/
def veroneseDegreeOneImageGenerates (d : ℕ) (ℒ : Y.Modules)
    [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ) : Prop :=
  Epi ((ℒ.freeHomEquiv).symm (veroneseDegreeOneSectionFamily 𝒜 d ℒ ψ))

/-- Generation by the degree-one image is equivalent to epimorphy of the associated evaluation
map from the free module. -/
theorem veroneseDegreeOneImageGenerates_iff (d : ℕ) (ℒ : Y.Modules)
    [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ) :
    veroneseDegreeOneImageGenerates 𝒜 d ℒ ψ ↔
      Epi ((ℒ.freeHomEquiv).symm (veroneseDegreeOneSectionFamily 𝒜 d ℒ ψ)) := sorry

/-- A raw map to a positive-degree open is twist-compatible with a graded section map when every
positive-degree witness and every explicit twist presentation gives a unique compatible
line-bundle isomorphism. -/
def degreeOpenTwistCompatibility (d : ℕ) (ℒ : Y.Modules)
    [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ)
    (φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme) : Prop :=
  ∀ (hd : 1 ≤ d) (P : ProjTwistPresentation 𝒜),
    let x : Proj.DegreeOpenFactorization 𝒜 Y :=
      { degree := d, positive := hd, map := φd }
    ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅ ℒ,
      Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x ℒ ψ α

/-- Twist compatibility is characterized by a unique compatible isomorphism from the pulled-back
degree twist to the invertible module for every positivity witness and twist presentation. -/
theorem degreeOpenTwistCompatibility_iff (d : ℕ) (ℒ : Y.Modules)
    [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ)
    (φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme) :
    degreeOpenTwistCompatibility 𝒜 d ℒ ψ φd ↔
      ∀ (hd : 1 ≤ d) (P : ProjTwistPresentation 𝒜),
      let x : Proj.DegreeOpenFactorization 𝒜 Y :=
        { degree := d, positive := hd, map := φd }
      ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅ ℒ,
        Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x ℒ ψ α := sorry

/-- A grading-preserving Veronese map whose degree-one image generates an invertible module
determines a unique morphism to the corresponding degree open and, for a fixed twist
presentation, a unique compatible isomorphism from the pulled-back twist. -/
theorem existsUnique_degreeOpenMorphismAndTwistIso_of_veroneseSectionMap
    (P : ProjTwistPresentation 𝒜) (d : ℕ) (hd : 1 ≤ d)
    (ℒ : Y.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : GradedRing.Veronese 𝒜 d →+* RingedSpace.GradedSections.ring ℒ)
    (hgraded : veroneseSectionMapPreservesDegree 𝒜 d ℒ ψ)
    (hgen : veroneseDegreeOneImageGenerates 𝒜 d ℒ ψ) :
    ∃! φd : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme,
      let x : Proj.DegreeOpenFactorization 𝒜 Y :=
        { degree := d, positive := hd, map := φd }
      ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅ ℒ,
        Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x ℒ ψ α := sorry

end AlgebraicGeometry
