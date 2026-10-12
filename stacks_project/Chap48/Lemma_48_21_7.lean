/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/- Lemma 48.21.7: for a Cohen–Macaulay morphism, the compactification model of
`f⁺!𝒪_Y` is locally the relative dualizing module shifted by the locally constant
relative dimension; that module is coherent and flat over `Y`. -/
@[stacks 0BV8] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.exists_dualizingModule_of_cohenMacaulay :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      [AlgebraicGeometry.CohenMacaulay f.hom.left]
      (P : Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)),
      ∃ d : LocallyConstant X.obj.left ℕ,
        ∃ ω : RingedSpace.Modules (LocallyRingedSpace.toRingedSpace
            (Scheme.toLocallyRingedSpace X.obj.left)),
          (∀ x : X.obj.left,
            fiberDimensionAt f.hom.left x = (d x : WithBot ℕ∞)) ∧
          ω.IsCoherent ∧
          SheafOfModules.IsFlatOver ω
            (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f.hom.left)) ∧
          RingedSpace.ModuleDerived.IsLocallyShiftedSingle
            (dualizingObject f P A).obj ω d)

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
