/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.SingularGenusZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom AlgebraicGeometry.RingedSpace.Module.Skyscraper
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.10.5: a singular proper genus-zero curve whose global functions are the
ground field is obtained from a projective line over a nontrivial finite field extension
by identifying its distinguished rational point with a rational point of the curve. -/
@[stacks 0DJB] #check (AlgebraicGeometry.SchemeOverField.exists_projectiveLineNormalization :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [Curve X] → [IsProper X.hom] →
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) →
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0) →
    (h_singular : ¬ Scheme.Regular X.left) →
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k')
      (h_nontrivial : ¬ Function.Surjective (algebraMap k k'))
      (X' : SchemeOverField k')
      (h_projectiveLine : Nonempty (X' ≅ ProjectiveSpace.schemeOver k' 1))
      (ν : X'.left ⟶ X.left)
      (x' : SchemeOverField.point k' ⟶ X')
      (x : SchemeOverField.point k ⟶ X)
      (h_base : X'.hom ≫ FieldExtension.specMap k k' = ν ≫ X.hom)
      (h_point : SchemeOverField.rationalPoint x' ≫ ν =
        FieldExtension.specMap k k' ≫ SchemeOverField.rationalPoint x)
      (h_x_singular : ¬ IsRegularLocalRing
        (stalkRing X
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))))
      (U : X.left.Opens) (U' : X'.left.Opens)
      (hU : (U : Set X.left) =
        {SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k)}ᶜ)
      (hU' : (U' : Set X'.left) =
        {SchemeOverField.rationalPoint x' (IsLocalRing.closedPoint k')}ᶜ)
      (h_preimage : ν ⁻¹ᵁ U = U')
      (h_restrict : IsIso (ν ∣_ U))
      (q : (Scheme.Modules.pushforward ν).obj
          (SheafOfModules.unit X'.left.ringCatSheaf : X'.left.Modules) ⟶
        atPoint
          (SchemeOverField.rationalPoint x (IsLocalRing.closedPoint k))
          ((ModuleCat.restrictScalars
            (Scheme.stalkClosedPointTo
              (SchemeOverField.rationalPoint x)).hom).obj
            (ModuleCat.of k
              (k' ⧸ LinearMap.range (Algebra.linearMap k k')))))
      (h_zero : SheafOfModules.unitToPushforwardObjUnit
          (toRingCatSheafHom ν.toShHom) ≫ q = 0),
      (ShortComplex.mk
        (SheafOfModules.unitToPushforwardObjUnit
          (toRingCatSheafHom ν.toShHom)) q h_zero).ShortExact)

end AlgebraicGeometry.SchemeOverField
