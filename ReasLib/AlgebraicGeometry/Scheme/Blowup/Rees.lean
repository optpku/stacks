module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization
public import ReasLib.RingTheory.ReesAlgebra.Grading.Decomposition

/-!
# Blowups as relative projective spectra

This file packages the Rees graded-algebra presentation of a blowup.  Besides identifying the
nonnegative graded pieces with powers of the center ideal sheaf, the presentation records that
the graded unit and multiplication are the canonical operations after inclusion in the
structure sheaf.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

variable {X X' : Scheme.{u}} {I : X.IdealSheafData}

namespace Scheme.Hom

namespace ReesPresentation

/-- The map induced on top sections after restricting a module morphism along an open
immersion. -/
noncomputable abbrev restrictedMapOnTop
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    {M N : Z.Modules} (g : M ⟶ N) :
    Γ(Scheme.Modules.restrict M j, ⊤) → Γ(Scheme.Modules.restrict N j, ⊤) :=
  fun s ↦ (((Scheme.Modules.restrictFunctor j).map g).val.app (Opposite.op ⊤)).hom s

/-- The canonical first-twist section associated to a degree-one element of an affine Rees
algebra. -/
noncomputable def reesDegreeOneSection
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    Γ(Proj.AssociatedModule.twistingSheaf
      (ReesAlgebra.Grading.grade (I.ideal U)) 1, ⊤) :=
  Proj.AssociatedModule.degreeZeroToGlobalSections
    (ReesAlgebra.Grading.grade (I.ideal U))
    (GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading
        (ReesAlgebra.Grading.grade (I.ideal U))) 1)
    ⟨ReesAlgebra.Grading.degreeOne (I.ideal U) a, by
      simpa using ReesAlgebra.Grading.degreeOne_mem (I.ideal U) a⟩

end ReesPresentation

/-- A Rees presentation of a morphism consists of a relative projective-spectrum presentation
whose nonnegative degree pieces are the powers of an ideal sheaf, with unit and multiplication
agreeing with those of the structure sheaf after the canonical ideal inclusions. -/
structure ReesPresentation (f : X' ⟶ X) (I : X.IdealSheafData) where
  /-- The underlying presentation as a relative projective spectrum. -/
  toRelativeProjPresentation : RelativeProjPresentation f
  /-- The degree-`n` piece is canonically identified with the module represented by `I ^ n`. -/
  degreePieceIso : ∀ n : ℕ,
    toRelativeProjPresentation.degreePiece n ≅ (I ^ n).toModule
  /-- Over every affine open, the inverse image is canonically the projective spectrum of the
  Rees algebra of the corresponding ideal of sections. -/
  affineOpenIso : ∀ U : X.affineOpens,
    (f ⁻¹ᵁ (U : X.Opens)).toScheme ≅ Proj (ReesAlgebra.Grading.grade (I.ideal U))
  /-- The universal degree-one morphism from the pullback of the center ideal to the first
  relative twist. -/
  degreeOneMap :
    (Scheme.Modules.pullback f).obj I.toModule ⟶ toRelativeProjPresentation.twist 1
  /-- On an affine base open, the relative first twist agrees with the pullback of the canonical
  first twisting sheaf on the projective spectrum of the Rees algebra. -/
  affineTwistOneIso : ∀ U : X.affineOpens,
    (Scheme.Modules.pullback (affineOpenIso U).hom).obj
        (Proj.AssociatedModule.twistingSheaf
          (ReesAlgebra.Grading.grade (I.ideal U)) 1) ≅
      Scheme.Modules.restrict (toRelativeProjPresentation.twist 1)
        (f ⁻¹ᵁ (U : X.Opens)).ι
  /-- The canonical morphism from the inverse-image center ideal to the first relative twist. -/
  exceptionalIdealToTwistOne :
    (I.comap f).toModule ⟶ toRelativeProjPresentation.twist 1
  /-- Factoring the pulled-back center ideal through its image and then mapping to the first
  twist recovers the universal degree-one morphism. -/
  exceptionalIdealToTwistOne_fac :
    LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
        eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
          (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
      exceptionalIdealToTwistOne = degreeOneMap
  /-- On every affine Rees chart, the exceptional-ideal morphism sends a local lift of a center
  element to its canonical degree-one twisting-sheaf section. -/
  exceptionalIdealToTwistOne_affine :
    ∀ (U : X.affineOpens) (a : I.ideal U)
      (s : (Scheme.Modules.restrict
        ((Scheme.Modules.pullback f).obj I.toModule)
        (f ⁻¹ᵁ (U : X.Opens)).ι).val.obj (Opposite.op ⊤)),
      HEq
          ((Scheme.Modules.restrictAppIso (f ⁻¹ᵁ (U : X.Opens)).ι
            (SheafOfModules.unit X'.ringCatSheaf) ⊤).hom
            (ReesPresentation.restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
              (LocallyRingedSpace.IdealSubobject.pullbackMap
                I.toSubobject f.toLRSHom) s))
          ((f.app (U : X.Opens)).hom a.1) →
        (ReesPresentation.restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
          (LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
            eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
              (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
            exceptionalIdealToTwistOne) s =
          ((affineTwistOneIso U).hom.val.app (Opposite.op ⊤)).hom
            ((Scheme.Modules.globalSectionsPullback (affineOpenIso U).hom
              (Proj.AssociatedModule.twistingSheaf
                (ReesAlgebra.Grading.grade (I.ideal U)) 1)).hom
              (ReesPresentation.reesDegreeOneSection I U a)))
  /-- The degree-zero unit becomes `1` after transport to `I ^ 0` and inclusion in the
  structure sheaf. -/
  one_compatibility :
    ∀ U : X.Opensᵒᵖ,
      SheafOfModules.unitSectionToRingSection U.unop
        (((I ^ 0).toSubobject.arrow.val.app U).hom
          (((degreePieceIso 0).hom.val.app U).hom
            (toRelativeProjPresentation.algebra.one U))) = 1
  /-- Homogeneous multiplication becomes multiplication in the structure sheaf after transport
  to ideal powers and the canonical ideal inclusions. -/
  mul_compatibility :
    ∀ (U : X.Opensᵒᵖ) (n m : ℕ)
      (a : (toRelativeProjPresentation.degreePiece n).val.obj U)
      (b : (toRelativeProjPresentation.degreePiece m).val.obj U),
      SheafOfModules.unitSectionToRingSection U.unop
          (((I ^ (n + m)).toSubobject.arrow.val.app U).hom
            (((degreePieceIso (n + m)).hom.val.app U).hom
              (toRelativeProjPresentation.algebra.mul
                U (Int.ofNat n) (Int.ofNat m) a b))) =
        SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ n).toSubobject.arrow.val.app U).hom
              (((degreePieceIso n).hom.val.app U).hom a)) *
          SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ m).toSubobject.arrow.val.app U).hom
              (((degreePieceIso m).hom.val.app U).hom b))

namespace ReesPresentation

/-- Construct a Rees presentation from a relative projective-spectrum presentation, its
degree-piece and affine-open identifications, and the compatibility of the graded unit and
multiplication. -/
def of (P : RelativeProjPresentation (X := X') (S := X) f)
    (e : ∀ n : ℕ, P.degreePiece n ≅ (I ^ n).toModule)
    (affineOpenIso : ∀ U : X.affineOpens,
      (f ⁻¹ᵁ (U : X.Opens)).toScheme ≅ Proj (ReesAlgebra.Grading.grade (I.ideal U)))
    (degreeOneMap : (Scheme.Modules.pullback f).obj I.toModule ⟶ P.twist 1)
    (affineTwistOneIso : ∀ U : X.affineOpens,
      (Scheme.Modules.pullback (affineOpenIso U).hom).obj
          (Proj.AssociatedModule.twistingSheaf
            (ReesAlgebra.Grading.grade (I.ideal U)) 1) ≅
        Scheme.Modules.restrict (P.twist 1) (f ⁻¹ᵁ (U : X.Opens)).ι)
    (exceptionalIdealToTwistOne : (I.comap f).toModule ⟶ P.twist 1)
    (exceptionalIdealToTwistOne_fac :
      LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
          eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
            (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
        exceptionalIdealToTwistOne = degreeOneMap)
    (exceptionalIdealToTwistOne_affine :
      ∀ (U : X.affineOpens) (a : I.ideal U)
        (s : (Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj I.toModule)
          (f ⁻¹ᵁ (U : X.Opens)).ι).val.obj (Opposite.op ⊤)),
        HEq
            ((Scheme.Modules.restrictAppIso (f ⁻¹ᵁ (U : X.Opens)).ι
              (SheafOfModules.unit X'.ringCatSheaf) ⊤).hom
              (restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
                (LocallyRingedSpace.IdealSubobject.pullbackMap
                  I.toSubobject f.toLRSHom) s))
            ((f.app (U : X.Opens)).hom a.1) →
          (restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
            (LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
              eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
                (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
              exceptionalIdealToTwistOne) s =
            ((affineTwistOneIso U).hom.val.app (Opposite.op ⊤)).hom
              ((Scheme.Modules.globalSectionsPullback (affineOpenIso U).hom
                (Proj.AssociatedModule.twistingSheaf
                  (ReesAlgebra.Grading.grade (I.ideal U)) 1)).hom
                (reesDegreeOneSection I U a))))
    (h_one : ∀ U : X.Opensᵒᵖ,
      SheafOfModules.unitSectionToRingSection U.unop
        (((I ^ 0).toSubobject.arrow.val.app U).hom
          (((e 0).hom.val.app U).hom (P.algebra.one U))) = 1)
    (h_mul : ∀ (U : X.Opensᵒᵖ) (n m : ℕ)
      (a : (P.degreePiece n).val.obj U) (b : (P.degreePiece m).val.obj U),
      SheafOfModules.unitSectionToRingSection U.unop
          (((I ^ (n + m)).toSubobject.arrow.val.app U).hom
            (((e (n + m)).hom.val.app U).hom
              (P.algebra.mul U (Int.ofNat n) (Int.ofNat m) a b))) =
        SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ n).toSubobject.arrow.val.app U).hom (((e n).hom.val.app U).hom a)) *
          SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ m).toSubobject.arrow.val.app U).hom (((e m).hom.val.app U).hom b))) :
    ReesPresentation f I where
  toRelativeProjPresentation := P
  degreePieceIso := e
  affineOpenIso := affineOpenIso
  degreeOneMap := degreeOneMap
  affineTwistOneIso := affineTwistOneIso
  exceptionalIdealToTwistOne := exceptionalIdealToTwistOne
  exceptionalIdealToTwistOne_fac := exceptionalIdealToTwistOne_fac
  exceptionalIdealToTwistOne_affine := exceptionalIdealToTwistOne_affine
  one_compatibility := h_one
  mul_compatibility := h_mul

/-- The unit, multiplication, exceptional-ideal factorization, and affine degree-one laws of a
Rees presentation hold simultaneously. -/
theorem spec (P : ReesPresentation f I) :
    (∀ U : X.Opensᵒᵖ,
      SheafOfModules.unitSectionToRingSection U.unop
        (((I ^ 0).toSubobject.arrow.val.app U).hom
          (((P.degreePieceIso 0).hom.val.app U).hom
            (P.toRelativeProjPresentation.algebra.one U))) = 1) ∧
    (∀ (U : X.Opensᵒᵖ) (n m : ℕ)
      (a : (P.toRelativeProjPresentation.degreePiece n).val.obj U)
      (b : (P.toRelativeProjPresentation.degreePiece m).val.obj U),
      SheafOfModules.unitSectionToRingSection U.unop
          (((I ^ (n + m)).toSubobject.arrow.val.app U).hom
            (((P.degreePieceIso (n + m)).hom.val.app U).hom
              (P.toRelativeProjPresentation.algebra.mul
                U (Int.ofNat n) (Int.ofNat m) a b))) =
        SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ n).toSubobject.arrow.val.app U).hom
              (((P.degreePieceIso n).hom.val.app U).hom a)) *
          SheafOfModules.unitSectionToRingSection U.unop
            (((I ^ m).toSubobject.arrow.val.app U).hom
              (((P.degreePieceIso m).hom.val.app U).hom b))) ∧
    (LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
          eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
            (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
        P.exceptionalIdealToTwistOne = P.degreeOneMap) ∧
    (∀ (U : X.affineOpens) (a : I.ideal U)
      (s : (Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj I.toModule)
        (f ⁻¹ᵁ (U : X.Opens)).ι).val.obj (Opposite.op ⊤)),
      HEq
          ((Scheme.Modules.restrictAppIso (f ⁻¹ᵁ (U : X.Opens)).ι
            (SheafOfModules.unit X'.ringCatSheaf) ⊤).hom
            (restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
              (LocallyRingedSpace.IdealSubobject.pullbackMap
                I.toSubobject f.toLRSHom) s))
          ((f.app (U : X.Opens)).hom a.1) →
        (restrictedMapOnTop (f ⁻¹ᵁ (U : X.Opens)).ι
          (LocallyRingedSpace.IdealSubobject.pullbackFactor I.toSubobject f.toLRSHom ≫
            eqToHom (congrArg (fun J : Scheme.IdealSubobject X' ↦ J.toModule)
              (Scheme.IdealSheafData.toSubobject_comap I f).symm) ≫
            P.exceptionalIdealToTwistOne) s =
          ((P.affineTwistOneIso U).hom.val.app (Opposite.op ⊤)).hom
            ((Scheme.Modules.globalSectionsPullback (P.affineOpenIso U).hom
              (Proj.AssociatedModule.twistingSheaf
                (ReesAlgebra.Grading.grade (I.ideal U)) 1)).hom
              (reesDegreeOneSection I U a)))) :=
  ⟨P.one_compatibility, P.mul_compatibility,
    P.exceptionalIdealToTwistOne_fac, P.exceptionalIdealToTwistOne_affine⟩

end ReesPresentation

end Scheme.Hom

/-- A chosen blowup of `X` in the ideal sheaf `I`, carrying both its universal property and an
explicit Rees relative projective-spectrum presentation. -/
structure Blowup (X : Scheme.{u}) (I : X.IdealSheafData) extends Over X where
  /-- The structural morphism satisfies the blowup universal property for the center `I`. -/
  isBlowup : IsBlowup hom I
  /-- The structural morphism is explicitly presented by the Rees algebra of `I`. -/
  reesPresentation : Scheme.Hom.ReesPresentation hom I

namespace Blowup

/-- Bundle a morphism, its blowup universal property, and its Rees presentation as a chosen
blowup. -/
def of (f : X' ⟶ X) (h : IsBlowup f I) (P : Scheme.Hom.ReesPresentation f I) : Blowup X I where
  left := X'
  right := ⟨⟨⟩⟩
  hom := f
  isBlowup := h
  reesPresentation := P

/-- The underlying scheme of a chosen blowup. -/
abbrev scheme (π : Blowup X I) : Scheme.{u} :=
  π.left

/-- The exceptional divisor of a blowup is the inverse-image center ideal sheaf. -/
noncomputable abbrev exceptionalDivisor (π : Blowup X I) : π.scheme.IdealSheafData :=
  I.comap π.hom

/-- The exceptional divisor is the pullback of the center ideal sheaf along the blowup morphism. -/
theorem exceptionalDivisor_def (π : Blowup X I) :
    π.exceptionalDivisor = I.comap π.hom :=
  rfl

end Blowup

end

end AlgebraicGeometry
