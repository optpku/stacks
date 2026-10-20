module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.Descent
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Topology of field-extension base changes

This file records range comparison and compactness descent for base changes of schemes over
fields.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FieldExtension.Over

/-- Field-extension base change identifies the preimage of the range of a morphism over the
base field with the range of its base change. -/
theorem preimage_range_map
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X' X : AlgebraicGeometry.SchemeOverField k} (i : X' ⟶ X) :
    (toSource k K X) ⁻¹' Set.range i.left =
      Set.range (((functor k K).map i).left) := by
  change (Limits.pullback.fst X.hom (FieldExtension.specMap k K)) ⁻¹' Set.range i.left =
    Set.range
      (Limits.pullback.map X'.hom (FieldExtension.specMap k K) X.hom
        (FieldExtension.specMap k K) i.left (𝟙 _) (𝟙 _)
        (by simpa using Over.w i) (by simp))
  symm
  simpa [Set.range_id, Set.inter_eq_left] using
    (Scheme.Pullback.range_map X'.hom (FieldExtension.specMap k K) X.hom
      (FieldExtension.specMap k K) i.left (𝟙 _) (𝟙 _) (by simp) (by simp))

/-- Compactness of a field-extension base change descends to the original scheme over the base
field. -/
theorem compactSpace_of_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : AlgebraicGeometry.SchemeOverField k)
    [CompactSpace (baseChange k K X).left] :
    CompactSpace X.left := by
  let XK : AlgebraicGeometry.SchemeOverField K := baseChange k K X
  have hXK_qc : QuasiCompact XK.hom := by
    infer_instance
  have hSpecOpen : IsOpenMap (FieldExtension.specMap k K).base := by
    intro U hU
    simp
  have hX_qc : QuasiCompact X.hom := by
    exact QuasiCompact.of_isOpenMap_of_surjective_baseChange X.hom
      (FieldExtension.specMap k K) hSpecOpen hXK_qc
  exact QuasiCompact.compactSpace_of_compactSpace X.hom

end AlgebraicGeometry.FieldExtension.Over
