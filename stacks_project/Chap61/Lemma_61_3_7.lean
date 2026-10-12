/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/- Lemma 61.3.7: if `p : Y ⟶ X` and `q : Z ⟶ X` are morphisms of locally ringed
spaces and the canonical adjunct `p⁻¹ 𝒪_X ⟶ 𝒪_Y` is an isomorphism, then forgetting
sheaf maps yields a bijection from morphisms `Over.mk q ⟶ Over.mk p` in the slice
`Over X` to morphisms over `forgetToTop.obj X`, sending `(f, f♯)` to the
underlying continuous map `f`. -/
@[stacks 096K] #check
  (AlgebraicGeometry.LocallyRingedSpace.overPost_forgetToTop_map_bijective :
    ∀ {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X),
      IsIso (RingedSpace.Hom.inverseImageStructureSheafHomComm p.toShHom) →
        Function.Bijective fun φ : Over.mk q ⟶ Over.mk p ↦ (Over.post forgetToTop).map φ)

end AlgebraicGeometry.LocallyRingedSpace
