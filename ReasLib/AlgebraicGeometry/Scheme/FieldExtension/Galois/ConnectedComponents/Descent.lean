module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.ConnectedComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.ConnectedComponents

/-!
# Fixed connected components and geometric connectedness

This leaf gives direct-morphism forms of the fixed-component criterion for a separable closure.
Equality of underlying component subsets records the meaning of base change without relying only
on the induced quotient map on `ConnectedComponents`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Connected.Descent

/-- A connected component after a separable-closure base change is Galois-fixed exactly when it is
the inverse image of a geometrically connected connected component of the source. -/
@[stacks 038D]
theorem fixed_iff_exists
    {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : _root_.ConnectedComponents (FieldExtension.baseChange k ksep f)) :
    (∀ σ : Gal(ksep / k), σ • Tbar = Tbar) ↔
      ∃ C : _root_.ConnectedComponents X,
        GeometricallyConnected.Components.isConnected f C ∧
          (FieldExtension.toSource k ksep f).base ⁻¹' C.set = Tbar.set := sorry

/-- A connected component after a separable-closure base change is fixed by the opposite Galois
action exactly when it is the inverse image of a geometrically connected component. -/
@[stacks 038D]
theorem op_fixed_iff_exists
    {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : _root_.ConnectedComponents (FieldExtension.baseChange k ksep f)) :
    (∀ σ : (Gal(ksep / k))ᵐᵒᵖ, σ • Tbar = Tbar) ↔
      ∃ C : _root_.ConnectedComponents X,
        GeometricallyConnected.Components.isConnected f C ∧
          (FieldExtension.toSource k ksep f).base ⁻¹' C.set = Tbar.set := sorry

/-- Computational form of the fixed-component criterion using the induced map on connected
components. -/
@[stacks 038D]
theorem fixed_iff_exists_map
    {k ksep : Type u} [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : _root_.ConnectedComponents (FieldExtension.baseChange k ksep f)) :
    (∀ σ : Gal(ksep / k), σ • Tbar = Tbar) ↔
      ∃ C : _root_.ConnectedComponents X,
        GeometricallyConnected.Components.isConnected f C ∧
          Continuous.connectedComponentsMap
              ((FieldExtension.toSource k ksep f).continuous) Tbar = C := sorry

end FieldExtension.Galois.Connected.Descent

end AlgebraicGeometry
