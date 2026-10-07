module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.OpenRestriction.Completion
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w x

/- Remark 42.35.5 (1): the completion is the product, over source components, of the
finite-support nonnegative graded bivariant classes on the induced component morphisms. -/
@[stacks 0FE0] #check
  (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) {I : Type v} {J : Type w}
      (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
      (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)), Type (max (u + 1) v))

/- Remark 42.35.5 (2): compatible disjoint clopen decompositions identify the completion
with global degree families that vanish in almost all degrees on each source component. -/
@[stacks 0FE0] #check (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.globalEquiv :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)),
    AlgebraicGeometry.BivariantClass.OpenRestriction.Completion delta f U V a h ≃+
      AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.Global delta f U V a h)

/- Remark 42.35.5 (3): bivariant composition extends to componentwise completions and
agrees with completion of the ordinary nonnegative composition. -/
@[stacks 0FE0] #check (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.complete_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    {I : Type v} {J : Type w} {K : Type x}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (W : K → Z.left.Opens)
    (a : I → J) (b : J → K)
    (hUV : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (hVW : ∀ j, V j ≤ g.left ⁻¹ᵁ W (b j))
    (hUW : ∀ i, U i ≤ (f ≫ g).left ⁻¹ᵁ W (b (a i)))
    (c : AlgebraicGeometry.BivariantClass.Nonnegative delta f)
    (d : AlgebraicGeometry.BivariantClass.Nonnegative delta g),
    AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.complete delta
        (f ≫ g) U W (b ∘ a) hUW
        (AlgebraicGeometry.BivariantClass.Nonnegative.comp delta f g c d) =
      AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.comp delta
        f g U V W a b hUV hVW hUW
        (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.complete delta
          f U V a hUV c)
        (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.complete delta
          g V W b hVW d))

/- Remark 42.35.5 (4): multiplication in the completed cohomology ring is completed
bivariant composition for the identity morphism. -/
@[stacks 0FE0] #check (AlgebraicGeometry.ChowCohomology.completedRing_mul_eq_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i)
    (hIdComp : ∀ i, U i ≤ ((𝟙 X : X ⟶ X) ≫ 𝟙 X).left ⁻¹ᵁ U i)
    (c d : AlgebraicGeometry.ChowCohomology.completedRing delta X U
      hU_cover hU_disjoint hU_clopen hId),
    Eq.mp (AlgebraicGeometry.ChowCohomology.completedRing_eq_completion delta X U
        hU_cover hU_disjoint hU_clopen hId) (c * d) =
      Eq.mp (AlgebraicGeometry.ChowCohomology.identityCompCompletion_eq delta X U
        hId hIdComp)
        (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.comp delta
          (𝟙 X) (𝟙 X) U U U id id hId hId hIdComp
          (Eq.mp (AlgebraicGeometry.ChowCohomology.completedRing_eq_completion delta X U
            hU_cover hU_disjoint hU_clopen hId) c)
          (Eq.mp (AlgebraicGeometry.ChowCohomology.completedRing_eq_completion delta X U
            hU_cover hU_disjoint hU_clopen hId) d)))
