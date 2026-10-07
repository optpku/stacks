module

public import stacks_project.Chap85.Lemma_85_27_2_CartesianOver
public import stacks_project.Chap85.Lemma_85_27_4_Descent

/-!
# Lemma 85.27.4

A cartesian morphism of simplicial schemes over the Čech nerve of `f : X ⟶ S`
determines a descent datum relative to `f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ f.simplicialScheme)

/-- Lemma 85.27.4: let `f : X ⟶ S` be a morphism of schemes. Let
`π : Y ⟶ f.simplicialScheme` be a cartesian morphism of simplicial schemes.
Set `V = Y _⦋0⦌` considered as a scheme over `X`. The morphisms `Y.δ 0`, `Y.δ 1`
and `π.app (op ⦋1⦌)` induce isomorphisms `Y _⦋1⦌ ≅ V ×_S X` and
`Y _⦋1⦌ ≅ X ×_S V`. The resulting isomorphism `φ : V ×_S X ≅ X ×_S V`
makes `(V, φ)` a descent datum relative to `X ⟶ S`. -/
@[stacks 024B]
def ofCartesianHom [IsCartesian π] :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) where
  obj _ := schemeOver f π
  hom _ _ _ _ g₁ g₂ hf₁ hf₂ := comparisonHom f π g₁ g₂ (hf₁.trans hf₂.symm)
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The unique component object of `ofCartesianHom f π` is `schemeOver f π`. -/
theorem ofCartesianHom_obj [IsCartesian π] (i : PUnit.{v + 1}) :
    (ofCartesianHom f π).obj i = schemeOver f π := sorry

/-- Descent data attached to an object cartesian over the Čech nerve of `f`. -/
def ofCartesianOver (Y : CartesianOver f.simplicialScheme) :
    DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f) :=
  @ofCartesianHom _ _ f _ Y.obj.hom Y.property

/-- `ofCartesianOver` is `ofCartesianHom` of the underlying cartesian structure morphism. -/
theorem ofCartesianOver_eq (Y : CartesianOver f.simplicialScheme) :
    ofCartesianOver f Y = @ofCartesianHom _ _ f _ Y.obj.hom Y.property := sorry

end AlgebraicGeometry.Scheme.DescentData
