/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpenFactorization
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections
public import ReasLib.RingTheory.GradedAlgebra.Veronese.Basic

/-!
# Section maps from Veronese rings along degree-open factorizations

A positive-degree factorization into a projective spectrum determines degreewise pullback maps
from a Veronese ring.  An explicit multiplicatively coherent comparison between the pulled-back
twists and tensor powers assembles these maps into a homomorphism to the tensor-power section
ring.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.DegreeOpenFactorization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {Y : Scheme.{u}}

/-- The top-open sections of an actual twist pulled back along the morphism determined by a
degree-open factorization. -/
abbrev pullbackTwistSection (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) (n : ℤ) : Type u :=
  ((Scheme.Modules.pullback (x.toProj 𝒜)).obj (P.actualTwist n)).val.obj
    (op (⊤ : Y.Opens))

/-- The pulled-back actual-twist sections in the degrees selected by a Veronese grading. -/
abbrev pullbackVeroneseTwistSection (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) (n : ℕ) : Type u :=
  pullbackTwistSection 𝒜 P x (n * x.degree)

/-- The pullback of the chosen degree twist along the morphism determined by a degree-open
factorization. -/
abbrev lineBundle (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) : Y.Modules :=
  (Scheme.Modules.pullback (x.toProj 𝒜)).obj (P.actualTwist x.degree)

/-- A degreewise identification of pulled-back Veronese twists with tensor powers that preserves
the unit and homogeneous multiplication on global sections. -/
structure TwistComparison (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) where
  /-- The pulled-back actual twist in degree `n * d` is identified with the `n`th tensor power of
  the pulled-back degree-`d` twist. -/
  iso : ∀ n : ℕ,
    (Scheme.Modules.pullback (x.toProj 𝒜)).obj (P.actualTwist (n * x.degree)) ≅
      RingedSpace.TensorPower.sheaf (lineBundle 𝒜 P x) n
  /-- The degree-zero comparison carries the Veronese unit to the tensor-power section-ring
  unit. -/
  map_one :
    let degreeMap :=
      P.actualSectionMap (0 * x.degree) ≫
        Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
          (P.actualTwist (0 * x.degree)) ≫
        Scheme.Modules.globalSectionsMap (iso 0).hom
    DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) 0
        (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
      (1 : RingedSpace.GradedSections.ring (lineBundle 𝒜 P x))
  /-- The comparison carries homogeneous Veronese products to products in the tensor-power
  section ring. -/
  map_mul :
    let degreeMap := fun n ↦
      P.actualSectionMap (n * x.degree) ≫
        Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
          (P.actualTwist (n * x.degree)) ≫
        Scheme.Modules.globalSectionsMap (iso n).hom
    ∀ {i j : ℕ}
      (a : GradedRing.Veronese.degree 𝒜 x.degree i)
      (b : GradedRing.Veronese.degree 𝒜 x.degree j),
    DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) (i + j)
        ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
      DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) i
          ((degreeMap i).hom a) *
        DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) j
          ((degreeMap j).hom b)

namespace TwistComparison

/-- A family of degreewise twist isomorphisms satisfying the unit and multiplication laws
determines a coherent comparison with the tensor powers of the pulled-back degree twist. -/
def ofIso (P : ProjTwistPresentation 𝒜) (x : DegreeOpenFactorization 𝒜 Y)
    (iso : ∀ n : ℕ,
      (Scheme.Modules.pullback (x.toProj 𝒜)).obj (P.actualTwist (n * x.degree)) ≅
        RingedSpace.TensorPower.sheaf (lineBundle 𝒜 P x) n)
    (map_one :
      let degreeMap :=
        P.actualSectionMap (0 * x.degree) ≫
          Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (0 * x.degree)) ≫
          Scheme.Modules.globalSectionsMap (iso 0).hom
      DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) 0
          (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
        (1 : RingedSpace.GradedSections.ring (lineBundle 𝒜 P x)))
    (map_mul :
      let degreeMap := fun n ↦
        P.actualSectionMap (n * x.degree) ≫
          Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (n * x.degree)) ≫
          Scheme.Modules.globalSectionsMap (iso n).hom
      ∀ {i j : ℕ}
        (a : GradedRing.Veronese.degree 𝒜 x.degree i)
        (b : GradedRing.Veronese.degree 𝒜 x.degree j),
      DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) (i + j)
          ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
        DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) i
            ((degreeMap i).hom a) *
          DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) j
            ((degreeMap j).hom b)) :
    TwistComparison 𝒜 P x where
  iso := iso
  map_one := map_one
  map_mul := map_mul

/-- A coherent twist comparison satisfies both the unit and homogeneous multiplication
compatibility laws on global sections. -/
theorem spec (P : ProjTwistPresentation 𝒜) (x : DegreeOpenFactorization 𝒜 Y)
    (comparison : TwistComparison 𝒜 P x) :
    (let degreeMap :=
      P.actualSectionMap (0 * x.degree) ≫
        Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
          (P.actualTwist (0 * x.degree)) ≫
        Scheme.Modules.globalSectionsMap (comparison.iso 0).hom
    DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) 0
        (degreeMap.hom (GradedRing.Veronese.one 𝒜 x.degree)) =
      (1 : RingedSpace.GradedSections.ring (lineBundle 𝒜 P x))) ∧
      (let degreeMap := fun n ↦
        P.actualSectionMap (n * x.degree) ≫
          Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
            (P.actualTwist (n * x.degree)) ≫
          Scheme.Modules.globalSectionsMap (comparison.iso n).hom
      ∀ {i j : ℕ}
        (a : GradedRing.Veronese.degree 𝒜 x.degree i)
        (b : GradedRing.Veronese.degree 𝒜 x.degree j),
      DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) (i + j)
          ((degreeMap (i + j)).hom (GradedRing.Veronese.mul 𝒜 x.degree i j a b)) =
        DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) i
            ((degreeMap i).hom a) *
          DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) j
            ((degreeMap j).hom b)) := sorry

end TwistComparison

/-- The degree-`n` map from a Veronese piece to the global sections of the corresponding tensor
power of the pulled-back degree twist. -/
abbrev psiDegreeMap (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) (comparison : TwistComparison 𝒜 P x)
    (n : ℕ) :
    AddCommGrpCat.of (GradedRing.Veronese.degree 𝒜 x.degree n) ⟶
      AddCommGrpCat.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x) n) :=
  P.actualSectionMap (n * x.degree) ≫
    Scheme.Modules.globalSectionsPullback (x.toProj 𝒜)
      (P.actualTwist (n * x.degree)) ≫
    Scheme.Modules.globalSectionsMap (comparison.iso n).hom

/-- The homomorphism from the Veronese ring to the tensor-power section ring induced by a
degree-open factorization and a coherent twist comparison. -/
noncomputable def psi (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) (comparison : TwistComparison 𝒜 P x) :
    GradedRing.Veronese 𝒜 x.degree →+*
      RingedSpace.GradedSections.ring (lineBundle 𝒜 P x) :=
  DirectSum.toSemiring
    (fun n ↦
      (DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) n).comp
        (AddCommGrpCat.Hom.hom (psiDegreeMap 𝒜 P x comparison n)))
    comparison.map_one comparison.map_mul

/-- On a homogeneous element, the induced section-ring homomorphism applies the degreewise map
and includes its value in the same degree. -/
theorem psi_of (P : ProjTwistPresentation 𝒜)
    (x : DegreeOpenFactorization 𝒜 Y) (comparison : TwistComparison 𝒜 P x)
    (n : ℕ) (a : GradedRing.Veronese.degree 𝒜 x.degree n) :
    psi 𝒜 P x comparison
        (DirectSum.of (GradedRing.Veronese.degree 𝒜 x.degree) n a) =
      DirectSum.of (RingedSpace.GradedSections.degree (lineBundle 𝒜 P x)) n
        ((psiDegreeMap 𝒜 P x comparison n).hom a) := sorry

end AlgebraicGeometry.Proj.DegreeOpenFactorization
