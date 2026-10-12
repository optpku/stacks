/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOpenSections
import StacksCheckRecall

@[expose] public section

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

open CategoryTheory

namespace AlgebraicGeometry

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

/-- The `d`th Veronese subring of a graded ring, with degree-`n` piece `𝒜 (n * d)`. -/
abbrev projMorphismVeronese (d : ℕ) : Type u :=
  GradedRing.Veronese 𝒜 d

/-- A factorization of a fixed morphism to `Proj 𝒜` through the degree-`d` open. -/
structure ProjMorphismPsiFactorization (φ : Y ⟶ Proj 𝒜) (d : ℕ) where
  /-- The morphism from the source scheme to the degree-`d` open. -/
  toDegreeOpen : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme
  /-- The composite through the degree-`d` open is the original morphism. -/
  fac : toDegreeOpen ≫ (Proj.degreeOpen 𝒜 d).ι = φ

namespace ProjMorphismPsiFactorization

/-- A morphism to a degree open gives the corresponding factorization of its composite with the
open immersion into `Proj 𝒜`. -/
def forComposite (d : ℕ) (toDegreeOpen : Y ⟶ (Proj.degreeOpen 𝒜 d).toScheme) :
    ProjMorphismPsiFactorization 𝒜
      (toDegreeOpen ≫ (Proj.degreeOpen 𝒜 d).ι) d where
  toDegreeOpen := toDegreeOpen
  fac := rfl

/-- The stored lift of a factorization composes with the degree-open immersion to the fixed
morphism into `Proj 𝒜`. -/
theorem spec {φ : Y ⟶ Proj 𝒜} {d : ℕ}
    (factorization : ProjMorphismPsiFactorization 𝒜 φ d) :
    factorization.toDegreeOpen ≫ (Proj.degreeOpen 𝒜 d).ι = φ :=
  factorization.fac

end ProjMorphismPsiFactorization

/-- A degreewise identification of the iterated pullback of the degree-`n * d` twist with the
`n`th tensor power of the iterated pullback of the degree-`d` twist. -/
structure ProjMorphismPsiComparison (P : ProjTwistPresentation 𝒜)
    (φ : Y ⟶ Proj 𝒜) (d : ℕ) (factorization : ProjMorphismPsiFactorization 𝒜 φ d) where
  /-- The comparison between the iterated pullback twist and the corresponding tensor power. -/
  iso : ∀ n : ℕ,
    (Scheme.Modules.pullback factorization.toDegreeOpen).obj
        ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
          (P.actualTwist (n * d))) ≅
      RingedSpace.TensorPower.sheaf
        ((Scheme.Modules.pullback factorization.toDegreeOpen).obj
          ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
            (P.actualTwist d))) n

namespace ProjMorphismPsiComparison

/-- A family of isomorphisms between the iterated pullback twists and tensor powers determines
the corresponding degreewise comparison. -/
def ofIso (P : ProjTwistPresentation 𝒜) {φ : Y ⟶ Proj 𝒜} {d : ℕ}
    (factorization : ProjMorphismPsiFactorization 𝒜 φ d)
    (iso : ∀ n : ℕ,
      (Scheme.Modules.pullback factorization.toDegreeOpen).obj
          ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
            (P.actualTwist (n * d))) ≅
        RingedSpace.TensorPower.sheaf
          ((Scheme.Modules.pullback factorization.toDegreeOpen).obj
            ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
              (P.actualTwist d))) n) :
    ProjMorphismPsiComparison 𝒜 P φ d factorization where
  iso := iso

end ProjMorphismPsiComparison

/-- The degree-`n` section map obtained by restricting the degree-`n * d` twist to the degree
open and then pulling it back along a chosen factorization. -/
noncomputable def projMorphismPsiDegreeMap (P : ProjTwistPresentation 𝒜)
    (φ : Y ⟶ Proj 𝒜) (d : ℕ) (factorization : ProjMorphismPsiFactorization 𝒜 φ d)
    (n : ℕ) :
    AddCommGrpCat.of (𝒜 (n * d)) ⟶
      Scheme.Modules.globalSections
        ((Scheme.Modules.pullback factorization.toDegreeOpen).obj
          ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
            (P.actualTwist (n * d)))) :=
  P.actualSectionMap (n * d) ≫
    Scheme.Modules.globalSectionsPullback (Proj.degreeOpen 𝒜 d).ι
      (P.actualTwist (n * d)) ≫
    Scheme.Modules.globalSectionsPullback factorization.toDegreeOpen
      ((Scheme.Modules.pullback (Proj.degreeOpen 𝒜 d).ι).obj
        (P.actualTwist (n * d)))

end AlgebraicGeometry

#check (GradedRing.Veronese :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → ℕ → Type u)

#check (GradedRing.Veronese.one :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    GradedRing.Veronese.degree 𝒜 d 0)

#check (GradedRing.Veronese.mul :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d m n : ℕ) →
    GradedRing.Veronese.degree 𝒜 d m →
      GradedRing.Veronese.degree 𝒜 d n →
        GradedRing.Veronese.degree 𝒜 d (m + n))

#check (GradedRing.Veronese.instGOne :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    GradedMonoid.GOne (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGNonUnitalNonAssocSemiring :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    DirectSum.GNonUnitalNonAssocSemiring (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGMonoid :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    GradedMonoid.GMonoid (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGCommMonoid :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    GradedMonoid.GCommMonoid (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGSemiring :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    DirectSum.GSemiring (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGRing :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    DirectSum.GRing (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGCommSemiring :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    DirectSum.GCommSemiring (GradedRing.Veronese.degree 𝒜 d))

#check (GradedRing.Veronese.instGCommRing :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → (d : ℕ) →
    DirectSum.GCommRing (GradedRing.Veronese.degree 𝒜 d))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → AlgebraicGeometry.Scheme.{u} → Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullbackTwistSection :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.ProjTwistPresentation 𝒜 →
      AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y → ℤ → Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullbackVeroneseTwistSection :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.ProjTwistPresentation 𝒜 →
      AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y → ℕ → Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.ProjTwistPresentation 𝒜 →
      AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y → Y.Modules)

#check (AlgebraicGeometry.RingedSpace.GradedSections.degree :
  {X : AlgebraicGeometry.RingedSpace.{u}} → X.Modules → ℕ → Type u)

#check (AlgebraicGeometry.RingedSpace.GradedSections.ring :
  {X : AlgebraicGeometry.RingedSpace.{u}} → X.Modules → Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
    AlgebraicGeometry.ProjTwistPresentation 𝒜 →
      AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y → Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison.ofIso :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (P : AlgebraicGeometry.ProjTwistPresentation 𝒜)
    (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y)
    (iso : ∀ n : ℕ,
      (AlgebraicGeometry.Scheme.Modules.pullback (x.toProj 𝒜)).obj
          (P.actualTwist (n * x.degree)) ≅
        AlgebraicGeometry.RingedSpace.TensorPower.sheaf
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x) n)
    (map_one :
      let degreeMap :=
        CategoryTheory.CategoryStruct.comp (P.actualSectionMap (0 * x.degree))
          (CategoryTheory.CategoryStruct.comp
            (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
              (P.actualTwist (0 * x.degree)))
            (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (iso 0).hom))
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) 0
          (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
        (1 : AlgebraicGeometry.RingedSpace.GradedSections.ring
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)))
    (map_mul :
      let degreeMap := fun n ↦
        CategoryTheory.CategoryStruct.comp (P.actualSectionMap (n * x.degree))
          (CategoryTheory.CategoryStruct.comp
            (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
              (P.actualTwist (n * x.degree)))
            (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (iso n).hom))
      ∀ {i j : ℕ}
        (a : GradedRing.Veronese.degree 𝒜 x.degree i)
        (b : GradedRing.Veronese.degree 𝒜 x.degree j),
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) (i + j)
          ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
        DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
            (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) i
            ((degreeMap i).hom a) *
          DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
            (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) j
            ((degreeMap j).hom b)),
    AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison.spec :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (P : AlgebraicGeometry.ProjTwistPresentation 𝒜)
    (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y)
    (comparison :
      AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x),
    (let degreeMap :=
      CategoryTheory.CategoryStruct.comp (P.actualSectionMap (0 * x.degree))
        (CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (0 * x.degree)))
          (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (comparison.iso 0).hom))
    DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) 0
        (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
      (1 : AlgebraicGeometry.RingedSpace.GradedSections.ring
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x))) ∧
      (let degreeMap := fun n ↦
        CategoryTheory.CategoryStruct.comp (P.actualSectionMap (n * x.degree))
          (CategoryTheory.CategoryStruct.comp
            (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
              (P.actualTwist (n * x.degree)))
            (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (comparison.iso n).hom))
      ∀ {i j : ℕ}
        (a : GradedRing.Veronese.degree 𝒜 x.degree i)
        (b : GradedRing.Veronese.degree 𝒜 x.degree j),
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) (i + j)
          ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
        DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
            (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) i
            ((degreeMap i).hom a) *
          DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
            (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) j
            ((degreeMap j).hom b)))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.psiDegreeMap :
  (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
    (P : AlgebraicGeometry.ProjTwistPresentation 𝒜) →
      (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y) →
        AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x →
          (n : ℕ) → AddCommGrpCat.of (GradedRing.Veronese.degree 𝒜 x.degree n) ⟶
            AddCommGrpCat.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
              (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x) n))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison.map_one :
  ∀ {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    {P : AlgebraicGeometry.ProjTwistPresentation 𝒜}
    {x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y}
    (self : AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x),
    let degreeMap :=
      CategoryTheory.CategoryStruct.comp (P.actualSectionMap (0 * x.degree))
        (CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (0 * x.degree)))
          (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (self.iso 0).hom))
    DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) 0
        (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
      (1 : AlgebraicGeometry.RingedSpace.GradedSections.ring
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison.map_mul :
  ∀ {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    {P : AlgebraicGeometry.ProjTwistPresentation 𝒜}
    {x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y}
    (self : AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x),
    let degreeMap := fun n ↦
      CategoryTheory.CategoryStruct.comp (P.actualSectionMap (n * x.degree))
        (CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (n * x.degree)))
          (AlgebraicGeometry.Scheme.Modules.globalSectionsMap (self.iso n).hom))
    ∀ {i j : ℕ}
      (a : GradedRing.Veronese.degree 𝒜 x.degree i)
      (b : GradedRing.Veronese.degree 𝒜 x.degree j),
    DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) (i + j)
        ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) i
          ((degreeMap i).hom a) *
        DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
          (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) j
          ((degreeMap j).hom b))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.psi_of :
  ∀ (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (P : AlgebraicGeometry.ProjTwistPresentation 𝒜)
    (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y)
    (comparison : AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x)
    (n : ℕ) (a : GradedRing.Veronese.degree 𝒜 x.degree n),
    AlgebraicGeometry.Proj.DegreeOpenFactorization.psi 𝒜 P x comparison
        (DirectSum.of (GradedRing.Veronese.degree 𝒜 x.degree) n a) =
      DirectSum.of (AlgebraicGeometry.RingedSpace.GradedSections.degree
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x)) n
        ((AlgebraicGeometry.Proj.DegreeOpenFactorization.psiDegreeMap
          𝒜 P x comparison n).hom a))

/- 27.12.0.3: For `φ = x.toProj 𝒜` and `d = x.degree`, the Veronese ring maps to the
tensor-power section ring of the pulled-back degree-`d` twist. -/
@[stacks 01N7] #check
  (AlgebraicGeometry.Proj.DegreeOpenFactorization.psi :
    (𝒜 : ℕ → σ) → [GradedRing 𝒜] → {Y : AlgebraicGeometry.Scheme.{u}} →
      (P : AlgebraicGeometry.ProjTwistPresentation 𝒜) →
        (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y) →
          (comparison :
            AlgebraicGeometry.Proj.DegreeOpenFactorization.TwistComparison 𝒜 P x) →
            GradedRing.Veronese 𝒜 x.degree →+*
              AlgebraicGeometry.RingedSpace.GradedSections.ring
                (AlgebraicGeometry.Proj.DegreeOpenFactorization.lineBundle 𝒜 P x))
