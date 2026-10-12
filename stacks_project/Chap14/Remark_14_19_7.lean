/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Extension.UniversalProperty
import StacksCheckRecall

@[expose] public section

/-!
@stack 0188

# Remark 14.19.7 compatibility facade

The universal face and degeneracy maps are owned by
`SimplicialObject.Truncated.matching.FaceFamily`; an actual one-step extension only supplies the
bridge identifying its transported structure maps with those canonical maps.
-/

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ T : C)
variable (R :
  (SimplicialObject.Truncated.matching.FaceFamily.presheaf U).RepresentableBy U_succ)
variable (i : Fin (n + 2)) (j : Fin (n + 1))
variable (g : T ⟶ U_succ)
variable (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)))

/- Remark 14.19.7 (1): on `T`-valued points, the universal faces are the coordinates of
the universal matching family represented by `U_succ`. -/
@[stacks 0188 "Remark 14.19.7 (1)"]
#check (SimplicialObject.Truncated.matching.FaceFamily.π.comp R i g :
  g ≫ SimplicialObject.Truncated.matching.FaceFamily.π R i =
    (R.homEquiv g).app i)

/- Remark 14.19.7 (2): a universal degeneracy is the morphism represented by the canonical
matching family induced by the corresponding degeneracy. -/
@[stacks 0188 "Remark 14.19.7 (2)"]
#check (SimplicialObject.Truncated.matching.FaceFamily.σ.comp R j f :
  f ≫ SimplicialObject.Truncated.matching.FaceFamily.σ R j =
    R.homEquiv.symm
      (SimplicialObject.Truncated.matching.FaceFamily.degeneracy U j f))

/- Remark 14.19.7 (3): its `i`-th face coordinate is the composite indexed by
`SimplexCategory.δ i ≫ SimplexCategory.σ j`. -/
@[stacks 0188 "Remark 14.19.7 (3)"]
#check (SimplicialObject.Truncated.matching.FaceFamily.σ.face R i j f :
  (R.homEquiv
      (f ≫ SimplicialObject.Truncated.matching.FaceFamily.σ R j)).app i =
    f ≫ U.map
      (SimplexCategory.Truncated.Hom.tr
        (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op)

/- Remark 14.19.7 (4): in degree zero the two face coordinates both recover `f`. -/
@[stacks 0188 "Remark 14.19.7 (4)"]
#check (SimplicialObject.Truncated.matching.FaceFamily.σ.zero :
  ∀ {U : SimplicialObject.Truncated C 0} {U_succ T : C}
    (R :
      (SimplicialObject.Truncated.matching.FaceFamily.presheaf U).RepresentableBy U_succ)
    (f : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))),
      (fun i : Fin 2 ↦
        (R.homEquiv
          (f ≫ SimplicialObject.Truncated.matching.FaceFamily.σ R 0)).app i) =
        fun _ : Fin 2 ↦ f)

variable (E : SimplicialObject.Truncated.matching.Extension R)

/- An actual extension face is its represented universal face. -/
#check SimplicialObject.Truncated.matching.Extension.face.eq_π E i

/- An actual extension degeneracy is its represented universal degeneracy. -/
#check SimplicialObject.Truncated.matching.Extension.degeneracy.eq_σ E j

end CategoryTheory
