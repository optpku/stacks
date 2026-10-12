/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.ProjectiveDeformation

open Scheme.Modules.Invertible

/-- An explicit truncated section-algebra presentation of a morphism as a relative projective
spectrum, together with its twist identification, vanishing, and finiteness properties. -/
structure Presentation.{u} (d₀ : ℕ) {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    (L' : X'.Modules) where
  /-- The lifted module is invertible. -/
  invertible : Scheme.Modules.Invertible L'
  /-- The presentation of `f′` as a relative projective spectrum. -/
  proj : Scheme.Hom.RelativeProjPresentation f'
  /-- The graded algebra structure on the twists of the relative-Proj presentation. -/
  twistAlgebra : Scheme.Hom.RelativeProjTwistAlgebra proj
  /-- The canonical multiplicative map from the defining algebra to its relative-Proj twists. -/
  projSectionHom : Scheme.RelativeProjTwist.Hom proj.algebra f'
    twistAlgebra.toGradedAlgebraSheaf
  /-- The canonical multiplicative map from the defining algebra to the pushed-forward
  integral powers of `L′`. -/
  sectionHom : Scheme.RelativeProjTwist.Hom proj.algebra f'
    (@RingedSpace.InvertiblePower.gradedAlgebra _ L'
      (ringedSpaceIsInvertible invertible))
  /-- The first Serre twist is the lifted invertible module. -/
  twistOneIso : proj.twist 1 ≅ L'
  /-- The degree-one twist identification intertwines the two canonical multiplicative section
  maps. -/
  twistOneIso_hom :
    projSectionHom.hom 1 ≫ (Scheme.Modules.pushforward f').map twistOneIso.hom =
      sectionHom.hom 1 ≫ (Scheme.Modules.pushforward f').map
        ((@RingedSpace.InvertiblePower.natIso _ L'
          (ringedSpaceIsInvertible invertible) 1).inv ≫
            (RingedSpace.TensorPower.oneIso L').hom)
  /-- The degree-zero piece is the structure sheaf of the base. -/
  degreeZeroIso : proj.algebra 0 ≅ SheafOfModules.unit S'.ringCatSheaf
  /-- Every negative graded piece vanishes. -/
  negativeDegreeIsZero : ∀ d : ℤ, d < 0 → IsZero (proj.algebra d)
  /-- Every positive graded piece below the cutoff vanishes. -/
  omittedPositiveDegreeIsZero :
    ∀ d : ℕ, 0 < d → d < d₀ → IsZero (proj.degreePiece d)
  /-- Above the cutoff, the graded pieces are the pushforwards of tensor powers of `L′`. -/
  degreeHighIso : ∀ d : ℕ, d₀ ≤ d →
    (proj.degreePiece d ≅
      (Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d))
  /-- Each high-degree identification is the isomorphism induced by the canonical multiplicative
  section map. -/
  degreeHighIso_hom : ∀ (d : ℕ) (hd : d₀ ≤ d),
    (degreeHighIso d hd).hom = sectionHom.hom d ≫
      (Scheme.Modules.pushforward f').map
        (@RingedSpace.InvertiblePower.natIso _ L'
          (ringedSpaceIsInvertible invertible) d).inv
  /-- All positive higher direct images of sufficiently high tensor powers vanish. -/
  higherDirectImageIsZero : ∀ (p d : ℕ), 0 < p → d₀ ≤ d →
    IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
      (RingedSpace.TensorPower.sheaf L' d) p)
  /-- The sufficiently high pushforwards are finite locally free. -/
  degreePieceIsFiniteLocallyFree : ∀ d : ℕ, d₀ ≤ d →
    SheafOfModules.IsFiniteLocallyFree
      ((Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d))
  /-- The defining graded algebra is degreewise quasi-coherent. -/
  algebraIsQuasicoherent : proj.algebra.IsQuasicoherent
  /-- Each verified affine chart presents the graded algebra by a finitely presented algebra. -/
  finitePresentationOnAffineCharts : ∀ s : S',
    (@AffineOpenSectionProj.sectionRingStructureMap S'
      (proj.affineChart s).affineAlgebra.ring (proj.affineChart s).affineAlgebra.grade
      (proj.affineChart s).affineAlgebra.ring.commRing
      (proj.affineChart s).affineAlgebra.gradeSetLike
      (proj.affineChart s).affineAlgebra.gradeAddSubgroupClass
      (proj.affineChart s).affineAlgebra.grading
      (proj.affineChart s).affineAlgebra.grading_inst proj.algebra
      (proj.affineChart s).baseOpen (proj.affineChart s).degreePieceSectionsIso
      (proj.affineChart s).isAffineOpenSectionModel).FinitePresentation

universe u

namespace Presentation

/-- Construct a deformation presentation from an explicit relative-Proj presentation, its
twist algebra and degree identifications, and the stated finiteness and vanishing properties. -/
def ofRelativeProj {d₀ : ℕ} {X' S' : Scheme.{u}} {f' : X' ⟶ S'} {L' : X'.Modules}
    (invertible : Scheme.Modules.Invertible L')
    (proj : Scheme.Hom.RelativeProjPresentation f')
    (twistAlgebra : Scheme.Hom.RelativeProjTwistAlgebra proj)
    (projSectionHom : Scheme.RelativeProjTwist.Hom proj.algebra f'
      twistAlgebra.toGradedAlgebraSheaf)
    (sectionHom : Scheme.RelativeProjTwist.Hom proj.algebra f'
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L'
        (ringedSpaceIsInvertible invertible)))
    (twistOneIso : proj.twist 1 ≅ L')
    (twistOneIso_hom :
      projSectionHom.hom 1 ≫ (Scheme.Modules.pushforward f').map twistOneIso.hom =
        sectionHom.hom 1 ≫ (Scheme.Modules.pushforward f').map
          ((@RingedSpace.InvertiblePower.natIso _ L'
            (ringedSpaceIsInvertible invertible) 1).inv ≫
              (RingedSpace.TensorPower.oneIso L').hom))
    (degreeZeroIso : proj.algebra 0 ≅ SheafOfModules.unit S'.ringCatSheaf)
    (negativeDegreeIsZero : ∀ d : ℤ, d < 0 → IsZero (proj.algebra d))
    (omittedPositiveDegreeIsZero :
      ∀ d : ℕ, 0 < d → d < d₀ → IsZero (proj.degreePiece d))
    (degreeHighIso : ∀ d : ℕ, d₀ ≤ d →
      (proj.degreePiece d ≅
        (Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d)))
    (degreeHighIso_hom : ∀ (d : ℕ) (hd : d₀ ≤ d),
      (degreeHighIso d hd).hom = sectionHom.hom d ≫
        (Scheme.Modules.pushforward f').map
          (@RingedSpace.InvertiblePower.natIso _ L'
            (ringedSpaceIsInvertible invertible) d).inv)
    (higherDirectImageIsZero : ∀ (p d : ℕ), 0 < p → d₀ ≤ d →
      IsZero (RingedSpace.Hom.higherDirectImageModule f'.toShHom
        (RingedSpace.TensorPower.sheaf L' d) p))
    (degreePieceIsFiniteLocallyFree : ∀ d : ℕ, d₀ ≤ d →
      SheafOfModules.IsFiniteLocallyFree
        ((Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d)))
    (algebraIsQuasicoherent : proj.algebra.IsQuasicoherent)
    (finitePresentationOnAffineCharts : ∀ s : S',
      (@AffineOpenSectionProj.sectionRingStructureMap S'
        (proj.affineChart s).affineAlgebra.ring (proj.affineChart s).affineAlgebra.grade
        (proj.affineChart s).affineAlgebra.ring.commRing
        (proj.affineChart s).affineAlgebra.gradeSetLike
        (proj.affineChart s).affineAlgebra.gradeAddSubgroupClass
        (proj.affineChart s).affineAlgebra.grading
        (proj.affineChart s).affineAlgebra.grading_inst proj.algebra
        (proj.affineChart s).baseOpen (proj.affineChart s).degreePieceSectionsIso
        (proj.affineChart s).isAffineOpenSectionModel).FinitePresentation) :
    Presentation d₀ f' L' where
  invertible := invertible
  proj := proj
  twistAlgebra := twistAlgebra
  projSectionHom := projSectionHom
  sectionHom := sectionHom
  twistOneIso := twistOneIso
  twistOneIso_hom := twistOneIso_hom
  degreeZeroIso := degreeZeroIso
  negativeDegreeIsZero := negativeDegreeIsZero
  omittedPositiveDegreeIsZero := omittedPositiveDegreeIsZero
  degreeHighIso := degreeHighIso
  degreeHighIso_hom := degreeHighIso_hom
  higherDirectImageIsZero := higherDirectImageIsZero
  degreePieceIsFiniteLocallyFree := degreePieceIsFiniteLocallyFree
  algebraIsQuasicoherent := algebraIsQuasicoherent
  finitePresentationOnAffineCharts := finitePresentationOnAffineCharts

/-- The degree-one twist of a base-changed presentation is the pullback of the lifted module. -/
noncomputable def baseChangeTwistOneIso
    {d₀ : ℕ} {X' S' T : Scheme.{u}} {f' : X' ⟶ S'} {L' : X'.Modules}
    (Q : Presentation d₀ f' L') (h : T ⟶ S')
    (B : Scheme.Hom.RelativeProjBaseChange Q.proj h) :
    B.presentation.twist 1 ≅
      (Scheme.Modules.pullback (pullback.fst f' h)).obj L' :=
  (B.theta.degreeIso 1).symm ≪≫
    (Scheme.Modules.pullback (pullback.fst f' h)).mapIso Q.twistOneIso

/-- Explicit functoriality data identifying the relative-Proj base change of a deformation
presentation with a presentation for the pulled-back lifted module. -/
structure BaseChange
    {d₀ : ℕ} {X' S' T : Scheme.{u}} {f' : X' ⟶ S'} {L' : X'.Modules}
    (Q : Presentation d₀ f' L') (h : T ⟶ S') where
  /-- The relative-Proj algebra and twist comparison along `h`. -/
  relativeProj : Scheme.Hom.RelativeProjBaseChange Q.proj h
  /-- The presentation obtained for the base-changed morphism and pulled-back module. -/
  target : Presentation d₀ (pullback.snd f' h)
    ((Scheme.Modules.pullback (pullback.fst f' h)).obj L')
  /-- The relative-Proj presentation in the comparison is the target presentation. -/
  presentation_eq : relativeProj.presentation = target.proj
  /-- The source twist algebra is the one carried by the original presentation. -/
  sourceTwistAlgebra_eq : relativeProj.sourceTwistAlgebra = Q.twistAlgebra
  /-- The transported twist algebra is the one carried by the target presentation. -/
  targetTwistAlgebra_eq : HEq relativeProj.twistAlgebra target.twistAlgebra
  /-- In high degrees, pullback commutes with the pushed-forward tensor powers. -/
  pushforwardIso : ∀ (d : ℕ), d₀ ≤ d →
    ((Scheme.Modules.pullback h).obj
        ((Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d)) ≅
      (Scheme.Modules.pushforward (pullback.snd f' h)).obj
        (RingedSpace.TensorPower.sheaf
          ((Scheme.Modules.pullback (pullback.fst f' h)).obj L') d))
  /-- The high-degree base-change isomorphisms intertwine the canonical multiplicative section
  homomorphisms. -/
  sectionHom_comm : ∀ (d : ℕ) (hd : d₀ ≤ d),
    (Scheme.Modules.pullback h).map
          (Q.sectionHom.hom d ≫ (Scheme.Modules.pushforward f').map
            (@RingedSpace.InvertiblePower.natIso _ L'
              (ringedSpaceIsInvertible Q.invertible) d).inv) ≫
        (pushforwardIso d hd).hom =
      (relativeProj.algebraPullback.degreeIso (Int.ofNat d)).hom ≫
        eqToHom (congrArg (fun P : Scheme.Hom.RelativeProjPresentation
          (pullback.snd f' h) ↦ P.algebra (Int.ofNat d)) presentation_eq) ≫
        target.sectionHom.hom d ≫
          (Scheme.Modules.pushforward (pullback.snd f' h)).map
            (@RingedSpace.InvertiblePower.natIso _
              ((Scheme.Modules.pullback (pullback.fst f' h)).obj L')
              (ringedSpaceIsInvertible target.invertible) d).inv
  /-- The transported degree-one twist identification is the target identification. -/
  twistOneIso_eq : HEq (Q.baseChangeTwistOneIso h relativeProj) target.twistOneIso

namespace BaseChange

/-- Construct functoriality data from explicit relative-Proj, presentation, high-degree
pushforward, section-map, and twist comparisons. -/
def ofRelativeProj
    {d₀ : ℕ} {X' S' T : Scheme.{u}} {f' : X' ⟶ S'} {L' : X'.Modules}
    {Q : Presentation d₀ f' L'} {h : T ⟶ S'}
    (relativeProj : Scheme.Hom.RelativeProjBaseChange Q.proj h)
    (target : Presentation d₀ (pullback.snd f' h)
      ((Scheme.Modules.pullback (pullback.fst f' h)).obj L'))
    (presentation_eq : relativeProj.presentation = target.proj)
    (sourceTwistAlgebra_eq : relativeProj.sourceTwistAlgebra = Q.twistAlgebra)
    (targetTwistAlgebra_eq : HEq relativeProj.twistAlgebra target.twistAlgebra)
    (pushforwardIso : ∀ (d : ℕ), d₀ ≤ d →
      ((Scheme.Modules.pullback h).obj
          ((Scheme.Modules.pushforward f').obj (RingedSpace.TensorPower.sheaf L' d)) ≅
        (Scheme.Modules.pushforward (pullback.snd f' h)).obj
          (RingedSpace.TensorPower.sheaf
            ((Scheme.Modules.pullback (pullback.fst f' h)).obj L') d)))
    (sectionHom_comm : ∀ (d : ℕ) (hd : d₀ ≤ d),
      (Scheme.Modules.pullback h).map
            (Q.sectionHom.hom d ≫ (Scheme.Modules.pushforward f').map
              (@RingedSpace.InvertiblePower.natIso _ L'
                (ringedSpaceIsInvertible Q.invertible) d).inv) ≫
          (pushforwardIso d hd).hom =
        (relativeProj.algebraPullback.degreeIso (Int.ofNat d)).hom ≫
          eqToHom (congrArg (fun P : Scheme.Hom.RelativeProjPresentation
            (pullback.snd f' h) ↦ P.algebra (Int.ofNat d)) presentation_eq) ≫
          target.sectionHom.hom d ≫
            (Scheme.Modules.pushforward (pullback.snd f' h)).map
              (@RingedSpace.InvertiblePower.natIso _
                ((Scheme.Modules.pullback (pullback.fst f' h)).obj L')
                (ringedSpaceIsInvertible target.invertible) d).inv)
    (twistOneIso_eq : HEq (Q.baseChangeTwistOneIso h relativeProj) target.twistOneIso) :
    BaseChange Q h where
  relativeProj := relativeProj
  target := target
  presentation_eq := presentation_eq
  sourceTwistAlgebra_eq := sourceTwistAlgebra_eq
  targetTwistAlgebra_eq := targetTwistAlgebra_eq
  pushforwardIso := pushforwardIso
  sectionHom_comm := sectionHom_comm
  twistOneIso_eq := twistOneIso_eq

end BaseChange

/-- A presentation of a proper, flat, finitely presented morphism has compatible truncated
section-algebra, relative-Proj, and twist data after every base change. -/
theorem existsBaseChange {d₀ : ℕ} {X' S' T : Scheme.{u}} {f' : X' ⟶ S'}
    [IsProper f'] [Flat f'] [Scheme.Hom.FinitePresentation f']
    {L' : X'.Modules} (Q : Presentation d₀ f' L') (h : T ⟶ S') :
    Nonempty (BaseChange Q h) := sorry

/-- The base-changed degree-one identification is the twist comparison followed by pullback of
the original identification. -/
theorem baseChangeTwistOneIso_def
    {d₀ : ℕ} {X' S' T : Scheme.{u}} {f' : X' ⟶ S'} {L' : X'.Modules}
    (Q : Presentation d₀ f' L') (h : T ⟶ S')
    (B : Scheme.Hom.RelativeProjBaseChange Q.proj h) :
    Q.baseChangeTwistOneIso h B =
      (B.theta.degreeIso 1).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst f' h)).mapIso Q.twistOneIso := sorry

end Presentation

/-- A proper, flat, finitely presented morphism carrying a relatively ample invertible module
over a quasi-compact base has a uniform cutoff for relative-Proj presentations of compatible
deformations, together with base-change comparison data for each presentation. -/
theorem existsPresentationBound
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [Scheme.Hom.FinitePresentation f] [CompactSpace S]
    (L : X.Modules) [RelativelyAmple f L] :
    ∃ d₀ : ℕ,
      ∀ {X' S' : Scheme.{u}} (iX : X ⟶ X') (f' : X' ⟶ S') (i : S ⟶ S')
        [IsThickening i] [IsProper f'] [Flat f'] [Scheme.Hom.FinitePresentation f'],
        (hcart : IsPullback f iX i f') →
          ∀ (L' : X'.Modules) [Scheme.Modules.Invertible L'],
            (liftIso : L ≅ (Scheme.Modules.pullback iX).obj L') →
              ∃ Q : Presentation d₀ f' L',
                ∀ {T : Scheme.{u}} (h : T ⟶ S'), Nonempty (Presentation.BaseChange Q h) := sorry

end AlgebraicGeometry.ProjectiveDeformation
