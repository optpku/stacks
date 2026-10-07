module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Graded
public import ReasLib.AlgebraicGeometry.Scheme.Module.InvertibleQuotient.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Lift
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.DegreeOneQuotient

/-!
# Symmetric presentations of projective bundles

A symmetric presentation identifies a relative projective spectrum with the
graded symmetric algebra and supplies an explicit degree-one twist
presentation.  The tautological invertible quotient is derived from that data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]

/-- An explicit symmetric-algebra presentation of a relative projective spectrum, together
with the raw degree-one twist data from which its tautological quotient is constructed. -/
structure SymmetricPresentation (π : P ⟶ X) (ℰ : X.Modules) where
  /-- The relative projective-spectrum presentation. -/
  relativeProj : Scheme.Hom.RelativeProjPresentation π
  /-- Every nonnegative homogeneous piece is identified with the corresponding symmetric
  power of `ℰ`. -/
  symmetricPieceIso : ∀ n : ℕ,
    (SheafOfModules.RingedSite.SymmetricPower.graded
      (Scheme.schemeCommRingSheaf X) ℰ).obj n ≅ relativeProj.degreePiece n
  /-- The degreewise identifications preserve the degree-zero unit. -/
  symmetricUnit_compatible : ∀ U : (Opens X)ᵒᵖ,
    (((symmetricPieceIso 0).hom.val.app U).hom
      ((SheafOfModules.RingedSite.SymmetricPower.graded
        (Scheme.schemeCommRingSheaf X) ℰ).one U)) = relativeProj.algebra.one U
  /-- The degreewise identifications preserve homogeneous multiplication. -/
  symmetricMul_compatible : ∀ (U : (Opens X)ᵒᵖ) (n m : ℕ)
      (a : ((SheafOfModules.RingedSite.SymmetricPower.graded
        (Scheme.schemeCommRingSheaf X) ℰ).obj n).val.obj U)
      (b : ((SheafOfModules.RingedSite.SymmetricPower.graded
        (Scheme.schemeCommRingSheaf X) ℰ).obj m).val.obj U),
    HEq
      (((symmetricPieceIso (n + m)).hom.val.app U).hom
        ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).mul U n m a b))
      (relativeProj.algebra.mul U (Int.ofNat n) (Int.ofNat m)
        (((symmetricPieceIso n).hom.val.app U).hom a)
        (((symmetricPieceIso m).hom.val.app U).hom b))
  /-- The explicit affine and relative-twist presentation in degree one. -/
  degreeOneTwist : Scheme.Hom.RelativeProjPresentation.DegreeOneTwist relativeProj

namespace SymmetricPresentation

/-- Construct a symmetric presentation from graded-symmetric identifications and explicit
degree-one twist data. -/
def ofCoordinates (π : P ⟶ X) (ℰ : X.Modules) [ℰ.IsQuasicoherent]
    (relativeProj : Scheme.Hom.RelativeProjPresentation π)
    (symmetricPieceIso : ∀ n : ℕ,
      (SheafOfModules.RingedSite.SymmetricPower.graded
        (Scheme.schemeCommRingSheaf X) ℰ).obj n ≅ relativeProj.degreePiece n)
    (symmetricUnit_compatible : ∀ U : (Opens X)ᵒᵖ,
      (((symmetricPieceIso 0).hom.val.app U).hom
        ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).one U)) = relativeProj.algebra.one U)
    (symmetricMul_compatible : ∀ (U : (Opens X)ᵒᵖ) (n m : ℕ)
        (a : ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).obj n).val.obj U)
        (b : ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).obj m).val.obj U),
      HEq
        (((symmetricPieceIso (n + m)).hom.val.app U).hom
          ((SheafOfModules.RingedSite.SymmetricPower.graded
            (Scheme.schemeCommRingSheaf X) ℰ).mul U n m a b))
        (relativeProj.algebra.mul U (Int.ofNat n) (Int.ofNat m)
          (((symmetricPieceIso n).hom.val.app U).hom a)
          (((symmetricPieceIso m).hom.val.app U).hom b)))
    (degreeOneTwist :
      Scheme.Hom.RelativeProjPresentation.DegreeOneTwist relativeProj) :
    SymmetricPresentation π ℰ :=
  { relativeProj
    symmetricPieceIso
    symmetricUnit_compatible
    symmetricMul_compatible
    degreeOneTwist }

/-- The degree-one piece of a symmetric presentation is canonically identified with `ℰ`. -/
noncomputable def degreeOneIso {π : P ⟶ X} (S : SymmetricPresentation π ℰ) :
    ℰ ≅ S.relativeProj.degreePiece 1 :=
  SheafOfModules.RingedSite.SymmetricPower.degreeOneIso
      (Scheme.schemeCommRingSheaf X) ℰ ≪≫ S.symmetricPieceIso 1

/-- The first twist serving as target of the tautological quotient. -/
noncomputable def tautologicalTarget {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) : P.Modules :=
  @Scheme.Hom.RelativeProjPresentation.DegreeOneTwist.twistOne
    X P π S.relativeProj S.degreeOneTwist

/-- The canonical tautological invertible quotient, obtained from the degree-one adjoint map
after transporting its source through the first-symmetric-power identification. -/
noncomputable def tautologicalQuotient {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback π).obj ℰ) :=
  CategoryTheory.InvertibleQuotient.precomposeIso
    ((Scheme.Modules.pullback π).mapIso S.degreeOneIso)
    (@Scheme.Hom.RelativeProjPresentation.DegreeOneTwist.quotient
      X P π S.relativeProj S.degreeOneTwist)

/-- The canonical tautological quotient morphism. -/
noncomputable def tautologicalMap {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    (Scheme.Modules.pullback π).obj ℰ ⟶ S.tautologicalTarget :=
  S.tautologicalQuotient.hom

/-- The concrete quotient on a test scheme obtained by pulling back the tautological quotient
along a lift and transporting its source through the lift triangle. -/
noncomputable def liftSourceQuotient {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ) :=
  CategoryTheory.InvertibleQuotient.precomposeIso
    (Lift.pullbackSourceIso σ ℰ).symm
    (CategoryTheory.InvertibleQuotient.pullback σ.hom S.tautologicalQuotient)

/-- The defining laws of a symmetric presentation consist of compatibility with the unit and
multiplication, together with degree-one generation of its affine models. -/
theorem spec {π : P ⟶ X} (S : SymmetricPresentation π ℰ) :
    (∀ U : (Opens X)ᵒᵖ,
      (((S.symmetricPieceIso 0).hom.val.app U).hom
        ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).one U)) = S.relativeProj.algebra.one U) ∧
      (∀ (U : (Opens X)ᵒᵖ) (n m : ℕ)
        (a : ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).obj n).val.obj U)
        (b : ((SheafOfModules.RingedSite.SymmetricPower.graded
          (Scheme.schemeCommRingSheaf X) ℰ).obj m).val.obj U),
        HEq
          (((S.symmetricPieceIso (n + m)).hom.val.app U).hom
            ((SheafOfModules.RingedSite.SymmetricPower.graded
              (Scheme.schemeCommRingSheaf X) ℰ).mul U n m a b))
          (S.relativeProj.algebra.mul U (Int.ofNat n) (Int.ofNat m)
            (((S.symmetricPieceIso n).hom.val.app U).hom a)
            (((S.symmetricPieceIso m).hom.val.app U).hom b))) ∧
      S.degreeOneTwist.GeneratedByDegreeOne := sorry

/-- The tautological quotient has the first twist as target and the transported canonical
degree-one adjoint as quotient morphism. -/
theorem tautologicalQuotient_spec {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    S.tautologicalQuotient.object = S.tautologicalTarget ∧
      S.tautologicalQuotient.hom =
        (Scheme.Modules.pullback π).map S.degreeOneIso.hom ≫
          (@Scheme.Hom.RelativeProjPresentation.DegreeOneTwist.degreeOneMap
            X P π S.relativeProj S.degreeOneTwist) := sorry

/-- The tautological map is the pullback of the first-symmetric-power identification followed
by the pullback-pushforward adjoint of the degree-one twist morphism. -/
theorem tautologicalMap_coordinate {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    S.tautologicalMap =
      (Scheme.Modules.pullback π).map S.degreeOneIso.hom ≫
        (@Scheme.Hom.RelativeProjPresentation.DegreeOneTwist.degreeOneMap
          X P π S.relativeProj S.degreeOneTwist) := sorry

end SymmetricPresentation

end AlgebraicGeometry.Scheme.ProjectiveBundle
