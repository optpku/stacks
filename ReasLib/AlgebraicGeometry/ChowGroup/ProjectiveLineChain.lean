/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.FunctionField

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineChain

variable (k : Type u) [Field k] {X : Scheme.{u}}
variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
variable (components : ℕ → (ProjectiveLine.scheme k ⟶ X))

/-- The singleton cycle at the image of `0 ∈ ℙ¹(k)` is a relative zero cycle. -/
theorem originSingleton_mem_dimensionSubgroup
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k) :
    @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        ((components 0).base (ProjectiveLine.zeroPoint k)) (1 : ℤ) ∈
      AlgebraicCycle.dimensionSubgroup
        (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) 0 := sorry

/-- The relative zero cycle supported at the origin of the first component. -/
noncomputable def originCycle
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k) :
    CycleGroup X
      (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) 0 :=
  ⟨@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
      ((components 0).base (ProjectiveLine.zeroPoint k)) (1 : ℤ),
    originSingleton_mem_dimensionSubgroup k p components h_over⟩

/-- The function-field map from the closure of a component's generic image to the closure of
the generic point of the projective line. -/
noncomputable def componentClosureFunctionFieldMap (j : ℕ) :
    (Scheme.PointClosure.scheme
        ((components j).base (genericPoint (ProjectiveLine.scheme k)))).functionField →+*
      (Scheme.PointClosure.scheme
        (genericPoint (ProjectiveLine.scheme k))).functionField :=
  (Scheme.PointClosure.map (components j) (genericPoint (ProjectiveLine.scheme k))).functionFieldMap
    (Scheme.Hom.map_genericPoint_eq_of_isDominant
      (Scheme.PointClosure.map (components j) (genericPoint (ProjectiveLine.scheme k))))

/-- The coordinate function on a component, obtained as the canonical inverse image of `Y / X`
under the function-field map induced by the component immersion. -/
noncomputable def coordinateOnComponent [∀ j, IsClosedImmersion (components j)] (j : ℕ) :
    (Scheme.PointClosure.scheme
        ((components j).base (genericPoint (ProjectiveLine.scheme k)))).functionFieldˣ :=
  Function.invFun
    (Units.map (componentClosureFunctionFieldMap k components j).toMonoidHom)
    (Units.map (ProjectiveLine.pointClosureFunctionFieldMap k).toMonoidHom
      (ProjectiveLine.coordinateFunction k))

/-- The chosen component coordinate pulls back to the standard coordinate `Y / X`. -/
theorem coordinateOnComponent_spec [∀ j, IsClosedImmersion (components j)] (j : ℕ) :
    Units.map (componentClosureFunctionFieldMap k components j).toMonoidHom
        (coordinateOnComponent k components j) =
      Units.map (ProjectiveLine.pointClosureFunctionFieldMap k).toMonoidHom
        (ProjectiveLine.coordinateFunction k) := sorry

/-- The component coordinate is uniquely determined by its pullback to the projective line. -/
theorem coordinateOnComponent_unique [∀ j, IsClosedImmersion (components j)] (j : ℕ)
    (f : (Scheme.PointClosure.scheme
      ((components j).base (genericPoint (ProjectiveLine.scheme k)))).functionFieldˣ)
    (hf : Units.map (componentClosureFunctionFieldMap k components j).toMonoidHom f =
      Units.map (ProjectiveLine.pointClosureFunctionFieldMap k).toMonoidHom
        (ProjectiveLine.coordinateFunction k)) :
    f = coordinateOnComponent k components j := sorry

/-- The generic image of every projective-line component has relative dimension one. -/
theorem componentGenericPoint_dimension [∀ j, IsClosedImmersion (components j)]
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k) (j : ℕ) :
    p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
        ((components j).base (genericPoint (ProjectiveLine.scheme k))) = 0 + 1 := sorry

/-- Local finiteness of the component images gives local finiteness of the closures of their
generic points. -/
theorem componentClosures_locallyFinite [∀ j, IsClosedImmersion (components j)]
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base) :
    LocallyFinite fun j ↦
      (Scheme.PointClosure.closedSubset
        ((components j).base (genericPoint (ProjectiveLine.scheme k))) : Set X) := sorry

/-- The locally finite principal boundary of the component coordinates telescopes to the
origin cycle of the first component. -/
theorem origin_eq_principalSum [∀ j, IsClosedImmersion (components j)]
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k)
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base)
    (h_node : ∀ j, (components j).base (ProjectiveLine.infinityPoint k) =
      (components (j + 1)).base (ProjectiveLine.zeroPoint k)) :
    originCycle k p components h_over =
      @RationalEquivalence.boundary X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) inferInstance 0 ℕ
        (fun j ↦ (components j).base (genericPoint (ProjectiveLine.scheme k)))
        (componentGenericPoint_dimension k p components h_over)
        (coordinateOnComponent k components)
        (componentClosures_locallyFinite k components h_local) := sorry

/-- For a locally finite covering chain of projective lines whose infinity point on each
component is identified with the zero point on the next, the first origin cycle is rationally
equivalent to zero. -/
theorem origin_rationallyEquivalent_zero
    [∀ j, IsClosedImmersion (components j)]
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k)
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base)
    (h_node : ∀ j, (components j).base (ProjectiveLine.infinityPoint k) =
      (components (j + 1)).base (ProjectiveLine.zeroPoint k))
    (h_cover : ∀ x : X, ∃ j y, (components j).base y = x) :
    @RationalEquivalence.RationallyEquivalent X
      (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) inferInstance 0
      (originCycle k p components h_over) 0 := sorry

/-- Every degree-zero Chow class vanishes for a locally finite covering chain of projective
lines with successive infinity and zero points identified. -/
theorem chowGroup_eq_zero
    [∀ j, IsClosedImmersion (components j)]
    (h_over : ∀ j, components j ≫ p = ProjectiveLine.toSpec k)
    (h_local : LocallyFinite fun j ↦ Set.range (components j).base)
    (h_node : ∀ j, (components j).base (ProjectiveLine.infinityPoint k) =
      (components (j + 1)).base (ProjectiveLine.zeroPoint k))
    (h_cover : ∀ x : X, ∃ j y, (components j).base y = x) :
    ∀ a : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) inferInstance 0,
      a = 0 := sorry

end AlgebraicGeometry.ProjectiveLineChain
