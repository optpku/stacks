module

public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.AlgebraicGeometry.Correspondence.Graph.Flat
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import Mathlib.CategoryTheory.Retract

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.GradedCategory.ProjectiveLine

/-- The degree-one graph class of the structure map of the projective line, capped
with its hyperplane class. -/
def tateInclusion (k : Type u) [Field k] :
    ofScheme (SchemeOverField.point k) (-1) ⟶ ofScheme (ProjectiveSpace.schemeOver k 1) 0 :=
  let X := SchemeOverField.point k
  let P : SchemeOverField k := Over.mk (ProjectiveSpace.toSpec k 1)
  let ℒ := ProjectiveSpace.twistingSheaf k 1 1
  let c := @ChowCohomology.firstChernClass _ _ (fun _ ↦ 0) (X ⨯ P).hom
    inferInstance inferInstance inferInstance
    ((Scheme.Modules.pullback (Limits.prod.snd : X ⨯ P ⟶ P).left).obj ℒ)
    (Scheme.Modules.Invertible.pullback (Limits.prod.snd : X ⨯ P ⟶ P).left
      (by dsimp [ℒ]; exact
        @AlgebraicGeometry.ProjectiveSpace.twistingSheaf.instInvertible k _ 1 1))
  Correspondence.castDegree (by norm_num : (1 : ℤ) = 0 - (-1))
    (BivariantClass.rationalize (fun _ ↦ 0) (Limits.prod.snd : X ⨯ P ⟶ P) 1
      (Correspondence.castHom (Category.id_comp (Limits.prod.snd : X ⨯ P ⟶ P)) 1
        ((add_zero (1 : ℤ)) ▸ BivariantClass.comp (fun _ ↦ 0) (𝟙 (X ⨯ P))
          Limits.prod.snd c (Correspondence.integralGraph (terminal.from P)))))

/-- The flat graph class of the structure map projects the projective line onto
the point Tate twist of index `-1`. -/
def tateProjection (k : Type u) [Field k] :
    ofScheme (ProjectiveSpace.schemeOver k 1) 0 ⟶ ofScheme (SchemeOverField.point k) (-1) :=
  Correspondence.castDegree (by norm_num : -(1 : ℤ) = (-1) - 0)
    (@Correspondence.rationalFlatGraph k _ (ProjectiveSpace.schemeOver k 1)
      (SchemeOverField.point k) _ _ _ (terminal.from (ProjectiveSpace.schemeOver k 1)) 1
      (by sorry) (by sorry))

/-- The point Tate twist is a retract of the projective line through the flat graph
and the hyperplane graph class. -/
def tateRetract (k : Type u) [Field k] :
    Retract (ofScheme (SchemeOverField.point k) (-1))
      (ofScheme (ProjectiveSpace.schemeOver k 1) 0) where
  i := tateInclusion k
  r := tateProjection k
  retract := sorry

/-- The inclusion in the Tate retraction is its hyperplane graph class. -/
theorem tateRetract_i (k : Type u) [Field k] :
    (tateRetract k).i = tateInclusion k := rfl

/-- The projection in the Tate retraction is its flat graph class. -/
theorem tateRetract_r (k : Type u) [Field k] :
    (tateRetract k).r = tateProjection k := rfl

end AlgebraicGeometry.Correspondence.GradedCategory.ProjectiveLine
