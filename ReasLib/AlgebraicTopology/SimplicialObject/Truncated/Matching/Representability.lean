module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Degeneracy
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Limit
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Represented matching face families

A representation of the matching face-family presheaf selects universal face and degeneracy
maps. The canonical matching object is the specialization supplied by the matching limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory.Truncated
open scoped Simplicial SimplexCategory.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace matching.FaceFamily

/-- The universal matching face family selected by a representation of the face-family
presheaf. -/
@[stacks 0188 "universal represented matching face family"]
def universal {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (presheaf U).RepresentableBy T) : FaceFamily U T :=
  R.homEquiv (𝟙 T)

/-- The `i`-th universal face map selected by a representation of the matching face-family
presheaf. -/
@[stacks 0188 "universal represented face map"]
def π {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (presheaf U).RepresentableBy T) (i : Fin (n + 2)) :
    T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) :=
  (universal R).app i

/-- Precomposing a universal face map gives the corresponding coordinate of the represented
matching family. -/
@[stacks 0188 "universal represented face on generalized points"]
theorem π.comp {n : ℕ} {U : SimplicialObject.Truncated C n} {T X : C}
    (R : (presheaf U).RepresentableBy T) (i : Fin (n + 2)) (g : X ⟶ T) :
    g ≫ π R i = (R.homEquiv g).app i := sorry

/-- The `j`-th universal degeneracy map selected by a representation of the matching
face-family presheaf. -/
@[stacks 0188 "universal represented degeneracy map"]
def σ {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (presheaf U).RepresentableBy T) (j : Fin (n + 1)) :
    U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ⟶ T :=
  R.homEquiv.symm (FaceFamily.degeneracy U j (𝟙 _))

/-- The represented matching family of a universal degeneracy is the canonical degeneracy
face family. -/
@[stacks 0188 "universal degeneracy representation"]
theorem σ.homEquiv {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (presheaf U).RepresentableBy T) (j : Fin (n + 1)) :
    R.homEquiv (σ R j) = FaceFamily.degeneracy U j (𝟙 _) := sorry

/-- Precomposing a universal degeneracy is the morphism represented by the corresponding
degeneracy face family. -/
@[stacks 0188 "universal degeneracy on generalized points"]
theorem σ.comp {n : ℕ} {U : SimplicialObject.Truncated C n} {T X : C}
    (R : (presheaf U).RepresentableBy T) (j : Fin (n + 1))
    (f : X ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    f ≫ σ R j = R.homEquiv.symm (FaceFamily.degeneracy U j f) := sorry

/-- The `i`-th face coordinate of a universal degeneracy is the simplicial composite indexed by
`δ_i ≫ σ_j`. -/
@[stacks 0188 "universal degeneracy face coordinate"]
theorem σ.face {n : ℕ} {U : SimplicialObject.Truncated C n} {T X : C}
    (R : (presheaf U).RepresentableBy T) (i : Fin (n + 2)) (j : Fin (n + 1))
    (f : X ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (R.homEquiv (f ≫ σ R j)).app i =
      f ≫ U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op := sorry

/-- In degree zero, both face coordinates of the universal degeneracy recover the original
morphism. -/
@[stacks 0188 "zero-degree universal degeneracy coordinates"]
theorem σ.zero {U : SimplicialObject.Truncated C 0} {T X : C}
    (R : (presheaf U).RepresentableBy T)
    (f : X ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (fun i : Fin 2 ↦ (R.homEquiv (f ≫ σ R 0)).app i) =
      fun _ : Fin 2 ↦ f := sorry

end matching.FaceFamily

namespace matching.object

namespace representableBy

/-- For the canonical matching-object representation, the universal represented face is the
corresponding matching-object projection. -/
@[simp, stacks 0189 "canonical matching representation on faces"]
theorem π {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] (i : Fin (n + 2)) :
    matching.FaceFamily.π (matching.object.representableBy U) i =
      matching.object.face U i := sorry

end representableBy

/-- The canonical `j`-th degeneracy into the matching object. -/
@[stacks 0189 "canonical matching-object degeneracy"]
noncomputable def σ {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] (j : Fin (n + 1)) :
    U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ⟶ matching.object U :=
  matching.FaceFamily.σ (matching.object.representableBy U) j

namespace σ

/-- The `i`-th face of the canonical matching-object degeneracy is induced by the simplicial
composite `δ_i ≫ σ_j`. -/
@[reassoc (attr := simp), stacks 0189 "canonical matching degeneracy face"]
theorem face {n : ℕ} (U : SimplicialObject.Truncated C n)
    [HasLimit (matching.diagram U)] (i : Fin (n + 2)) (j : Fin (n + 1)) :
    matching.object.σ U j ≫ matching.object.face U i =
      U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op := sorry

end σ

end matching.object

end CategoryTheory.SimplicialObject.Truncated
