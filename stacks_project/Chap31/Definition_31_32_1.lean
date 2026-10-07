module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
import StacksCheckRecall

universe u

/- Definition 31.32.1: the blowup of a scheme `X` in an ideal sheaf `I` is the relative Proj over
`X` of the graded algebra with degree-`n` piece `I ^ n`; its exceptional divisor is the
inverse-image ideal sheaf. -/
@[stacks 01OG] #check (AlgebraicGeometry.Blowup :
  (X : AlgebraicGeometry.Scheme.{u}) → X.IdealSheafData → Type (u + 1))

#check (AlgebraicGeometry.Blowup.reesPresentation :
  {X : AlgebraicGeometry.Scheme.{u}} → {I : X.IdealSheafData} →
    (π : AlgebraicGeometry.Blowup X I) →
      AlgebraicGeometry.Scheme.Hom.ReesPresentation π.hom I)

#check (AlgebraicGeometry.Scheme.Hom.ReesPresentation.degreePieceIso :
  {X X' : AlgebraicGeometry.Scheme.{u}} → {f : X' ⟶ X} →
    {I : X.IdealSheafData} →
      (P : AlgebraicGeometry.Scheme.Hom.ReesPresentation f I) → (n : ℕ) →
        P.toRelativeProjPresentation.degreePiece n ≅ (I ^ n).toModule)

#check (AlgebraicGeometry.Scheme.Hom.ReesPresentation.one_compatibility :
  {X X' : AlgebraicGeometry.Scheme.{u}} → {f : X' ⟶ X} →
    {I : X.IdealSheafData} → (P : AlgebraicGeometry.Scheme.Hom.ReesPresentation f I) →
      ∀ U : X.Opensᵒᵖ,
        SheafOfModules.unitSectionToRingSection U.unop
          (((I ^ 0).toSubobject.arrow.val.app U).hom
            (((P.degreePieceIso 0).hom.val.app U).hom
              (P.toRelativeProjPresentation.algebra.one U))) = 1)

#check (AlgebraicGeometry.Scheme.Hom.ReesPresentation.mul_compatibility :
  {X X' : AlgebraicGeometry.Scheme.{u}} → {f : X' ⟶ X} →
    {I : X.IdealSheafData} → (P : AlgebraicGeometry.Scheme.Hom.ReesPresentation f I) →
      ∀ (U : X.Opensᵒᵖ) (n m : ℕ)
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
                (((P.degreePieceIso m).hom.val.app U).hom b)))

#check (AlgebraicGeometry.Blowup.isBlowup :
  {X : AlgebraicGeometry.Scheme.{u}} → {I : X.IdealSheafData} →
    (π : AlgebraicGeometry.Blowup X I) → AlgebraicGeometry.IsBlowup π.hom I)

#check (AlgebraicGeometry.Blowup.exceptionalDivisor_def :
  {X : AlgebraicGeometry.Scheme.{u}} → {I : X.IdealSheafData} →
    (π : AlgebraicGeometry.Blowup X I) →
      π.exceptionalDivisor = I.comap π.hom)
