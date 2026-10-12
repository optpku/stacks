/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.AssociatedSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {S S' : AlgebraicGeometry.Scheme.{u}}
variable (D : S.IdealSheafData) (f : S' ⟶ S)
variable [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
variable [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι]

/- Lemma 31.14.5 (1): the pullback of the sheaf associated to an effective Cartier divisor is
canonically isomorphic to the sheaf associated to the pullback divisor. -/
@[stacks 0C4U] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.associatedSheafPullbackIso D f :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj D.associatedSheaf ≅
      (D.comap f).associatedSheaf)

/- Lemma 31.14.5 (2): the canonical pullback isomorphism carries the pullback of the canonical
section to the canonical section of the pullback divisor. -/
@[stacks 0C4U] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.associatedSheafPullbackIso_canonicalSection D f :
    SheafOfModules.sectionsMap (D.associatedSheafPullbackIso f).hom
        (AlgebraicGeometry.RingedSpace.Hom.pullbackSections
          f.toShHom D.canonicalSection) =
      (D.comap f).canonicalSection)
