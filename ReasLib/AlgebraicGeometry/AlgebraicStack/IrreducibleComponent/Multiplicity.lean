module

public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import Mathlib.Order.Lattice.Nat

/-!
# Multiplicities of irreducible components of algebraic stacks

The multiplicity of an irreducible component of a locally Noetherian algebraic
stack is the scheme-level multiplicity of any dominating smooth locally
Noetherian scheme chart. Independence of the chart is recorded separately; the
numerical value is observable `ℕ`-valued data.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A smooth locally Noetherian scheme chart dominating an irreducible component
of `|X|`. -/
structure ComponentChart {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {τ : TopologicalSpace (Points X)} (T : @irreducibleComponents (Points X) τ) where
  /-- The source scheme over `S`. -/
  U : Over S
  /-- The 1-morphism from the slice of `U` to `X`. -/
  hom : GroupoidsOver.slice U ⟶ X
  /-- An irreducible component of `U`. -/
  component : irreducibleComponents U.left
  /-- The chart morphism is smooth. -/
  smooth : Groupoids.Hom.Smooth hom
  /-- The source scheme is locally Noetherian. -/
  isLocallyNoetherian : AlgebraicGeometry.IsLocallyNoetherian U.left
  /-- The image of the component lands in `T`. -/
  mapsTo :
    Set.image (Points.mapOfSlice hom) (component : Set U.left) ⊆ (T : Set (Points X))

namespace ComponentChart

/-- Pack a smooth locally Noetherian scheme morphism and a dominating irreducible
component into a chart. -/
def of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {τ : TopologicalSpace (Points X)} {T : @irreducibleComponents (Points X) τ}
    {U : Over S} (hom : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth hom] [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (component : irreducibleComponents U.left)
    (mapsTo :
      Set.image (Points.mapOfSlice hom) (component : Set U.left) ⊆
        (T : Set (Points X))) :
    ComponentChart T where
  U := U
  hom := hom
  component := component
  smooth := inferInstance
  isLocallyNoetherian := inferInstance
  mapsTo := mapsTo

/-- The scheme-level multiplicity of the source component of a chart. -/
noncomputable def multiplicity {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ : TopologicalSpace (Points X)}
    {T : @irreducibleComponents (Points X) τ} (c : ComponentChart T) : ℕ :=
  @Scheme.irreducibleComponentMultiplicity c.U.left c.isLocallyNoetherian c.component

/-- Chart multiplicity is the scheme-level multiplicity of the source
component. -/
theorem multiplicity_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ : TopologicalSpace (Points X)}
    {T : @irreducibleComponents (Points X) τ} (c : ComponentChart T) :
    c.multiplicity =
      @Scheme.irreducibleComponentMultiplicity c.U.left c.isLocallyNoetherian
        c.component :=
  rfl

/-- The image of the chart component in `|X|` is contained in `T`. -/
theorem mapsTo_image_subset {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ : TopologicalSpace (Points X)}
    {T : @irreducibleComponents (Points X) τ} (c : ComponentChart T) :
    Set.image (Points.mapOfSlice c.hom) (c.component : Set c.U.left) ⊆
      (T : Set (Points X)) :=
  c.mapsTo

/-- A component chart is a smooth locally Noetherian scheme morphism whose
source component maps into `T`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {τ : TopologicalSpace (Points X)} {T : @irreducibleComponents (Points X) τ}
    (c : ComponentChart T) :
    Groupoids.Hom.Smooth c.hom ∧
      AlgebraicGeometry.IsLocallyNoetherian c.U.left ∧
        Set.image (Points.mapOfSlice c.hom) (c.component : Set c.U.left) ⊆
          (T : Set (Points X)) :=
  ⟨c.smooth, c.isLocallyNoetherian, c.mapsTo⟩

/-- Relative to a canonical topology, the closure of the image of the chart
component is the target component. -/
theorem closure_image_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {T : @irreducibleComponents (Points X) τ}
    (c : ComponentChart T) :
    @closure (Points X) τ
        (Set.image (Points.mapOfSlice c.hom) (c.component : Set c.U.left)) =
      (T : Set (Points X)) :=
  sorry

end ComponentChart

/-- The infimum of the scheme multiplicities of smooth component charts of an
irreducible component of a locally Noetherian algebraic stack. For a canonical
point topology, `irreducibleComponentMultiplicity_eq` identifies this number
with the multiplicity of every such chart. -/
noncomputable def irreducibleComponentMultiplicity {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsLocallyNoetherian X]
    (τ : TopologicalSpace (Points X))
    (T : @irreducibleComponents (Points X) τ) : ℕ :=
  sInf (setOf fun n : ℕ => ∃ c : ComponentChart T, c.multiplicity = n)

/-- The multiplicity of `T` in `X` equals the scheme-level multiplicity of the
source component of any dominating smooth chart. -/
theorem irreducibleComponentMultiplicity_eq {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : @irreducibleComponents (Points X) τ} (c : ComponentChart T) :
    irreducibleComponentMultiplicity X τ T = c.multiplicity :=
  sorry

/-- A locally Noetherian algebraic stack admits a dominating smooth scheme chart
for every irreducible component of `|X|`. -/
theorem exists_componentChart {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) :
    Nonempty (ComponentChart T) :=
  sorry

/-- The scheme-level multiplicity of a dominating chart is independent of the
choice of smooth morphism and of the source component. -/
@[stacks 0DR7]
theorem irreducibleComponentMultiplicity_independent {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : @irreducibleComponents (Points X) τ}
    (c₁ c₂ : ComponentChart T) :
    c₁.multiplicity = c₂.multiplicity :=
  sorry

/-- The identity slice of a locally Noetherian scheme recovers the scheme-level
multiplicity along `mapOfSlice`. -/
theorem irreducibleComponentMultiplicity_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    {τ : TopologicalSpace (Points (GroupoidsOver.slice U))}
    (hτ : IsPointsTopology (GroupoidsOver.slice U) τ)
    (T : @irreducibleComponents (Points (GroupoidsOver.slice U)) τ)
    (Z : irreducibleComponents U.left)
    (hZ :
      Set.image (Points.mapOfSlice (𝟙 (GroupoidsOver.slice U))) (Z : Set U.left) =
        (T : Set (Points (GroupoidsOver.slice U)))) :
    irreducibleComponentMultiplicity (GroupoidsOver.slice U) τ T =
      Scheme.irreducibleComponentMultiplicity U.left Z :=
  sorry

end AlgebraicGeometry.AlgebraicStack

