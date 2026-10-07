module

public import stacks_project.Chap85.Definition_85_27_3_Nerve
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Face pre-relation of a simplicial scheme over a morphism

The morphism `j = (Y.δ 1, Y.δ 0)` of a simplicial scheme `Y` over `f.simplicialScheme`
is recorded as a `Scheme.PreRelation` on `Y _⦋0⦌` over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open Scheme.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ f.simplicialScheme)

/-- The degree-`n` scheme of `Y` as an object of `Over S`, via `π` and the Čech-nerve
base projection of `f`. -/
def objOver (n : SimplexCategoryᵒᵖ) : Over S :=
  Over.mk (π.app n ≫ Arrow.cechNerve.base (Arrow.mk f) n)

/-- The structure morphism of `objOver f π n` is `π.app n` followed by the Čech-nerve
base projection. -/
theorem objOver_hom (n : SimplexCategoryᵒᵖ) :
    (objOver f π n).hom = π.app n ≫ Arrow.cechNerve.base (Arrow.mk f) n :=
  sorry

/-- Each face map `Y.δ i` is a morphism over `S`. -/
theorem face_comp_objOver (i : Fin 2) :
    Y.δ i ≫ (objOver f π (op ⦋0⦌)).hom = (objOver f π (op ⦋1⦌)).hom :=
  sorry

/-- The face map `Y.δ i` as a morphism of schemes over `S`. -/
def faceOver (i : Fin 2) :
    objOver f π (op ⦋1⦌) ⟶ objOver f π (op ⦋0⦌) :=
  Over.homMk (Y.δ i) (face_comp_objOver f π i)

/-- The underlying scheme morphism of `faceOver f π i` is `Y.δ i`. -/
theorem faceOver_left (i : Fin 2) :
    (faceOver f π i).left = Y.δ i :=
  sorry

/-- The pair `j = (Y.δ 1, Y.δ 0)` as a morphism over `S` into the product
`Y _⦋0⦌ ⨯_S Y _⦋0⦌`. -/
def facePair :
    objOver f π (op ⦋1⦌) ⟶ objOver f π (op ⦋0⦌) ⨯ objOver f π (op ⦋0⦌) :=
  prod.lift (faceOver f π 1) (faceOver f π 0)

/-- The first factor of `facePair f π` is the target face `Y.δ 1`. -/
theorem facePair_fst :
    facePair f π ≫ prod.fst = faceOver f π 1 :=
  sorry

/-- The second factor of `facePair f π` is the source face `Y.δ 0`. -/
theorem facePair_snd :
    facePair f π ≫ prod.snd = faceOver f π 0 :=
  sorry

/-- The two face maps `Y.δ 1` and `Y.δ 0` agree after composing with the structure map
of `Y _⦋0⦌` over `S`. -/
theorem facePair_comp :
    Y.δ (1 : Fin 2) ≫ (objOver f π (op ⦋0⦌)).hom =
      Y.δ (0 : Fin 2) ≫ (objOver f π (op ⦋0⦌)).hom :=
  sorry

/-- After identifying the product in `Over S` with the fibre product over `S`,
`facePair f π` recovers `j : Y _⦋1⦌ ⟶ Y _⦋0⦌ ×_S Y _⦋0⦌`. -/
theorem facePair_left :
    (facePair f π).left ≫
      (Over.prodLeftIsoPullback
        (objOver f π (op ⦋0⦌)) (objOver f π (op ⦋0⦌))).hom =
      pullback.lift (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) (facePair_comp f π) :=
  sorry

/-- The pre-relation on `Y _⦋0⦌` over `S` with defining map `j = (Y.δ 1, Y.δ 0)`. -/
def facePreRelation : Scheme.PreRelation (objOver f π (op ⦋0⦌)) :=
  ofHom (facePair f π)

/-- The target projection of `facePreRelation f π` is the face `Y.δ 1`. -/
theorem facePreRelation_t :
    (facePreRelation f π).t = faceOver f π 1 :=
  sorry

/-- The source projection of `facePreRelation f π` is the face `Y.δ 0`. -/
theorem facePreRelation_s :
    (facePreRelation f π).s = faceOver f π 0 :=
  sorry

/-- The defining arrow of `facePreRelation f π` is `facePair f π`. -/
theorem facePreRelation_hom :
    (facePreRelation f π).hom = facePair f π :=
  sorry

end AlgebraicGeometry.Scheme.Hom
