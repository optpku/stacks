module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.SchemeOverField CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalBridge

/-- The scheme over `K` obtained as the coproduct of the component schemes of a family of
rational bridges on the base change of `X` to `K`. -/
noncomputable def componentCoproduct
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X)) :
    SchemeOverField K :=
  Over.mk (Limits.Sigma.desc fun i : ι ↦
    (RationalBridge.componentScheme
      (FieldExtension.Over.baseChange k K X) (bridges i).component).hom)

/-- The structure morphism of `componentCoproduct` is the Sigma coproduct of the component
morphisms of the bridge family. -/
theorem componentCoproduct_hom
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X)) :
    (componentCoproduct K X bridges).hom =
      Limits.Sigma.desc fun i : ι ↦
        (RationalBridge.componentScheme
          (FieldExtension.Over.baseChange k K X) (bridges i).component).hom := sorry

/-- The canonical morphism from the coproduct of the summand components into the base-changed
scheme `X_K`. -/
noncomputable def componentCoproductMap
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X)) :
    (componentCoproduct K X bridges).left ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  Limits.Sigma.desc fun i : ι ↦
    (FieldExtension.Over.baseChange k K X).left.irreducibleComponentSubschemeι
      (bridges i).component

/-- The coproduct-to-`X_K` morphism is the Sigma descent of the component inclusions. -/
theorem componentCoproductMap_spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k)
    {ι : Type u}
    (bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X)) :
    componentCoproductMap K X bridges =
      Limits.Sigma.desc fun i : ι ↦
        (FieldExtension.Over.baseChange k K X).left.irreducibleComponentSubschemeι
          (bridges i).component := sorry

/-- The inclusion of the selected component after base change to `K`. -/
noncomputable def baseChangeComponentMap
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (B : RationalBridge X) :
    (FieldExtension.Over.baseChange k K (RationalBridge.componentScheme X B.component)).left ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  ((FieldExtension.Over.functor k K).map
    (Over.homMk (X.left.irreducibleComponentSubschemeι B.component) :
      RationalBridge.componentScheme X B.component ⟶ X)).left

/-- The selected-component map is obtained by applying field-extension base change to its
canonical inclusion into `X`. -/
theorem baseChangeComponentMap_spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (B : RationalBridge X) :
    baseChangeComponentMap K X B =
      ((FieldExtension.Over.functor k K).map
        (Over.homMk (X.left.irreducibleComponentSubschemeι B.component) :
          RationalBridge.componentScheme X B.component ⟶ X)).left := sorry

/-- Explicit finite coproduct data for the base change of a rational bridge component. -/
structure BaseChangeDecomposition
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (B : RationalBridge X) where
  /-- The finite indexing type of the rational-bridge summands. -/
  ι : Type u
  /-- Finiteness of the indexing type. -/
  finite : Finite ι
  /-- The rational bridges appearing as summands after base change to `K`. -/
  bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X)
  /-- Every summand lies in the component fibre of the selected bridge component. -/
  component_fiber :
    ∀ i : ι,
      FieldExtension.Irreducible.componentsMap k K X.hom (bridges i).component = B.component
  /-- An isomorphism from the base-changed component to the displayed coproduct. -/
  iso :
    FieldExtension.Over.baseChange k K (RationalBridge.componentScheme X B.component) ≅
      componentCoproduct K X bridges
  /-- The coproduct presentation agrees with the canonical inclusion into `X_K`. -/
  ambient_map_commutes :
    iso.hom.left ≫ componentCoproductMap K X bridges = baseChangeComponentMap K X B

namespace BaseChangeDecomposition

/-- Construct a finite coproduct decomposition from its explicit index, family, and isomorphism.
-/
def of
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) (B : RationalBridge X)
    (ι : Type u) (finite : Finite ι)
    (bridges : ι → RationalBridge (FieldExtension.Over.baseChange k K X))
    (component_fiber :
      ∀ i : ι,
        FieldExtension.Irreducible.componentsMap k K X.hom (bridges i).component = B.component)
    (iso :
      FieldExtension.Over.baseChange k K (RationalBridge.componentScheme X B.component) ≅
        componentCoproduct K X bridges)
    (ambient_map_commutes :
      iso.hom.left ≫ componentCoproductMap K X bridges = baseChangeComponentMap K X B) :
    BaseChangeDecomposition K X B :=
  { ι := ι
    finite := finite
    bridges := bridges
    component_fiber := component_fiber
    iso := iso
    ambient_map_commutes := ambient_map_commutes }

/-- The specification of a decomposition records finiteness and its coproduct presentation. -/
theorem spec
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    {X : SchemeOverField k} {B : RationalBridge X}
    (D : BaseChangeDecomposition K X B) :
    Finite D.ι ∧
      (∀ i : D.ι,
        FieldExtension.Irreducible.componentsMap k K X.hom (D.bridges i).component = B.component) ∧
      Nonempty
        (FieldExtension.Over.baseChange k K (RationalBridge.componentScheme X B.component) ≅
          componentCoproduct K X D.bridges) ∧
      D.iso.hom.left ≫ componentCoproductMap K X D.bridges = baseChangeComponentMap K X B := sorry

end BaseChangeDecomposition

/-- Over any field extension, a rational bridge on a proper one-dimensional at-worst-nodal
scheme with constant global functions admits a finite coproduct decomposition into rational
bridges compatible with the inclusion of its base-changed component. -/
theorem baseChange_decomposition
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (B : RationalBridge X) :
    Nonempty (RationalBridge.BaseChangeDecomposition K X B) := sorry


end RationalBridge

end AlgebraicGeometry
