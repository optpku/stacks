/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FlatQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/- Lemma 48.21.6: for a flat quasi-finite morphism, the compactification model of
`f⁺!𝒪_Y` is a coherent module flat over the target and placed in degree zero. -/
@[stacks 0BV7] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.exists_dualizingModule_of_flat_quasiFinite :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left]
      (P : Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)),
      ∃ ω : RingedSpace.Modules X.obj.left.toRingedSpace,
        ω.IsCoherent ∧
          SheafOfModules.IsFlatOver ω f.hom.left.toShHom ∧
            IsIsomorphic (dualizingObject f P A).obj
              ((DerivedCategory.singleFunctor X.obj.left.Modules 0).obj ω))

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
