/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u v w x

namespace AlgebraicGeometry.BivariantClass.OpenRestriction

/-- The product of finite-support nonnegative graded bivariant classes over source
components and their compatible target components. -/
abbrev Completion
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :=
  ∀ i, BivariantClass.Nonnegative delta
    (ComponentRestriction.hom f (U i) (V (a i)) (h i))

namespace Completion

/-- The completion carrier is the product of the componentwise direct sums. -/
theorem completion_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Completion delta f U V a h =
      (∀ i, BivariantClass.Nonnegative delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i))) := rfl

/-- Two completed classes are equal when all homogeneous component values agree. -/
@[ext]
theorem ext
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    {c d : Completion delta f U V a h} (heq : ∀ i p, c i p = d i p) : c = d := by
  funext i
  -- Local instance justification (defeq pin): DFinsupp.ext must use the component degree monoids fixed by Nonnegative, including their pointwise zeros.
  letI : ∀ p : ℕ, AddCommMonoid
      (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
        (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)).toAddCommMonoid
  exact DFinsupp.ext (heq i)

/-- Global nonnegative families whose restriction to each source component is nonzero in
only finitely many degrees. -/
def componentwiseFiniteSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :=
  -- Local instance justification (defeq pin): the subgroup laws on degree families must reduce to pointwiseZero, pointwiseAdd and pointwiseNeg for restriction.
  letI : ∀ p : ℕ, AddCommGroup (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ pointwiseAddCommGroup delta f (p : ℤ)
  ({ carrier := {c | ∀ i, {p : ℕ | ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) (c p) ≠
          pointwiseZero delta
            (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite}
     zero_mem' := by
       intro i
       change {p : ℕ | ComponentRestriction.restrict delta f (p : ℤ)
         (U i) (V (a i)) (h i) (pointwiseZero delta f (p : ℤ)) ≠
           pointwiseZero delta
             (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite
       simp only [ComponentRestriction.restrict_zero, ne_eq, not_true_eq_false,
         Set.setOf_false, Set.finite_empty]
     add_mem' := by
       intro c d hc hd i
       refine ((hc i).union (hd i)).subset ?_
       intro p hp
       by_contra hmem
       simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hmem
       apply hp
       change ComponentRestriction.restrict delta f (p : ℤ) (U i) (V (a i)) (h i)
         (pointwiseAdd delta f (p : ℤ) (c p) (d p)) = _
       rw [ComponentRestriction.restrict_add, hmem.1, hmem.2]
       -- Local instance justification (defeq pin): zero_add must use pointwiseAdd and pointwiseZero after rewriting restrict_add.
       letI := pointwiseAddCommGroup delta
         (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
       exact zero_add (0 : BivariantClass delta
         (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ))
     neg_mem' := by
       intro c hc i
       refine (hc i).subset ?_
       intro p hp
       by_contra hmem
       have hz : ComponentRestriction.restrict delta f (p : ℤ)
           (U i) (V (a i)) (h i) (c p) =
           pointwiseZero delta
             (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ) :=
         not_ne_iff.mp hmem
       -- Local instance justification (defeq pin): map_neg for components must use the product of the explicit component groups so its negation reduces to pointwiseNeg.
       letI : ∀ j, AddCommGroup
           (BivariantClass delta (ComponentRestriction.hom f (U j) (V (a j)) (h j))
             (p : ℤ)) :=
         fun j ↦ pointwiseAddCommGroup delta
           (ComponentRestriction.hom f (U j) (V (a j)) (h j)) (p : ℤ)
       have hn := congrFun
         (map_neg (ComponentRestriction.components delta f (p : ℤ) U V a h) (c p)) i
       apply hp
       change ComponentRestriction.restrict delta f (p : ℤ) (U i) (V (a i)) (h i)
         (pointwiseNeg delta f (p : ℤ) (c p)) = _
       change ComponentRestriction.restrict delta f (p : ℤ) (U i) (V (a i)) (h i)
         (pointwiseNeg delta f (p : ℤ) (c p)) =
           -ComponentRestriction.restrict delta f (p : ℤ) (U i) (V (a i)) (h i) (c p)
         at hn
       rw [hn, hz]
       exact neg_zero } : AddSubgroup (∀ p : ℕ, BivariantClass delta f (p : ℤ)))

/-- The carrier of componentwise-finite global nonnegative degree families. -/
abbrev Global
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :=
  componentwiseFiniteSubgroup delta f U V a h

/-- Membership in the global carrier is componentwise eventual vanishing. -/
theorem mem_componentwiseFiniteSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : ∀ p : ℕ, BivariantClass delta f (p : ℤ)) :
    c ∈ componentwiseFiniteSubgroup delta f U V a h ↔
      ∀ i, {p : ℕ | ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) (c p) ≠
          pointwiseZero delta
            (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite := Iff.rfl

/-- Assembling the restrictions of a bivariant class along compatible disjoint clopen
decompositions recovers the original class. -/
theorem componentsEquiv_leftInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Function.LeftInverse
      (ComponentRestriction.assemble delta f p U V a hU_cover hV_cover
        hU_disjoint hV_disjoint hU_clopen hV_clopen h)
      (ComponentRestriction.components delta f p U V a h) := sorry

/-- Restricting an assembled family along compatible disjoint clopen decompositions
recovers its component classes. -/
theorem componentsEquiv_rightInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Function.RightInverse
      (ComponentRestriction.assemble delta f p U V a hU_cover hV_cover
        hU_disjoint hV_disjoint hU_clopen hV_clopen h)
      (ComponentRestriction.components delta f p U V a h) := sorry

/-- In each degree, compatible disjoint clopen decompositions identify global classes with
their component restrictions. -/
noncomputable def componentsEquiv
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    @AddEquiv
      (BivariantClass delta f p)
      (∀ i, BivariantClass delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p)
      ({ add := pointwiseAdd delta f p } : Add (BivariantClass delta f p))
      (@Pi.instAdd I
        (fun i ↦ BivariantClass delta
          (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p)
        (fun i ↦ ({ add := (pointwiseAdd delta
          (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p) } :
            Add (BivariantClass delta
              (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p)))) :=
  -- Local instance justification (defeq pin): AddEquiv structure syntax and components.map_add' must use the source pointwiseAdd specified in the result type.
  letI := pointwiseAddCommGroup delta f p
  -- Local instance justification (defeq pin): AddEquiv structure syntax must use the product of component pointwiseAdd operations specified in the result type.
  letI : ∀ i, AddCommGroup
      (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p) :=
    fun i ↦ pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p
  { toFun := ComponentRestriction.components delta f p U V a h
    invFun := ComponentRestriction.assemble delta f p U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h
    left_inv := componentsEquiv_leftInverse delta f p U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h
    right_inv := componentsEquiv_rightInverse delta f p U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h
    map_add' := (ComponentRestriction.components delta f p U V a h).map_add' }

/-- A completed component family determines a global family degree by degree. -/
def globalFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : Completion delta f U V a h) : ∀ p : ℕ, BivariantClass delta f (p : ℤ) :=
  fun p ↦ (@AddEquiv.toEquiv _ _
    ({ add := pointwiseAdd delta f (p : ℤ) } : Add (BivariantClass delta f (p : ℤ)))
    (@Pi.instAdd I
      (fun i ↦ BivariantClass delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ))
      (fun i ↦ ({ add := (pointwiseAdd delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)) } :
          Add (BivariantClass delta
            (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)))))
    (componentsEquiv delta f (p : ℤ) U V a hU_cover hV_cover hU_disjoint
      hV_disjoint hU_clopen hV_clopen h)).symm.toFun (fun i ↦ c i p)

/-- The global family associated to a completion is componentwise finite. -/
theorem globalFamily_mem
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) (c : Completion delta f U V a h) :
    globalFamily delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
      hU_clopen hV_clopen h c ∈ componentwiseFiniteSubgroup delta f U V a h := by
  -- Local instance justification (defeq pin): apply_symm_apply must view componentsEquiv with its explicit global pointwiseAdd operation in each degree.
  letI : ∀ p : ℕ, AddCommGroup (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ pointwiseAddCommGroup delta f (p : ℤ)
  -- Local instance justification (defeq pin): apply_symm_apply must use the component pointwiseAdd operations matching componentsEquiv and the Nonnegative coefficients.
  letI : ∀ i, ∀ p : ℕ, AddCommGroup
      (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
        (p : ℤ)) :=
    fun i p ↦ pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
  intro i
  have heq (p : ℕ) : ComponentRestriction.restrict delta f (p : ℤ)
      (U i) (V (a i)) (h i)
      (globalFamily delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
        hU_clopen hV_clopen h c p) = c i p :=
    congrFun ((componentsEquiv delta f (p : ℤ) U V a hU_cover hV_cover hU_disjoint
      hV_disjoint hU_clopen hV_clopen h).apply_symm_apply (fun j ↦ c j p)) i
  have hfinite : {p : ℕ | c i p ≠ pointwiseZero delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite :=
    @DFinsupp.finite_support ℕ
      (fun p ↦ BivariantClass delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ))
      (fun p ↦ ⟨pointwiseZero delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)⟩) (c i)
  simpa only [heq] using hfinite

/-- The additive map from componentwise completion data to its global-family view. -/
def toGlobal
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Completion delta f U V a h →+ Global delta f U V a h where
  toFun c := ⟨globalFamily delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
    hU_clopen hV_clopen h c, globalFamily_mem delta f U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h c⟩
  map_zero' := by
    apply Subtype.ext
    funext p
    -- Local instance justification (defeq pin): assemble.map_zero' must reduce the global zero to pointwiseZero in this degree.
    letI := pointwiseAddCommGroup delta f (p : ℤ)
    -- Local instance justification (defeq pin): assemble.map_zero' must use the product zeros matching the component Nonnegative direct sums.
    letI : ∀ i, AddCommGroup
        (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
          (p : ℤ)) :=
      fun i ↦ pointwiseAddCommGroup delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
    exact (ComponentRestriction.assemble delta f (p : ℤ) U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h).map_zero'
  map_add' := by
    intro c d
    apply Subtype.ext
    funext p
    -- Local instance justification (defeq pin): assemble.map_add' must reduce global addition to pointwiseAdd in this degree.
    letI := pointwiseAddCommGroup delta f (p : ℤ)
    -- Local instance justification (defeq pin): assemble.map_add' must use the product additions matching the component Nonnegative direct sums.
    letI : ∀ i, AddCommGroup
        (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
          (p : ℤ)) :=
      fun i ↦ pointwiseAddCommGroup delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
    exact (ComponentRestriction.assemble delta f (p : ℤ) U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h).map_add'
        (fun i ↦ c i p) (fun i ↦ d i p)

private theorem directSum_mk_finite_apply
    {ι : Type*} {M : ι → Type*} [DecidableEq ι] [∀ i, AddCommMonoid (M i)]
    (c : ∀ i, M i) (hc : {i | c i ≠ 0}.Finite) (i : ι) :
    DirectSum.mk M hc.toFinset (fun j ↦ c j.1) i = c i := by
  by_cases hi : i ∈ hc.toFinset
  · exact DirectSum.mk_apply_of_mem hi
  · rw [DirectSum.mk_apply_of_notMem hi]
    exact (not_ne_iff.mp (by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      using hi)).symm

/-- Restrict a componentwise-finite global family degreewise to every source component. -/
def fromGlobal
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Global delta f U V a h →+ Completion delta f U V a h :=
  -- Local instance justification (defeq pin): DirectSum.mk and DirectSum.ext must use the degree monoids and zeros fixed by the component Nonnegative carrier.
  letI : ∀ i : I, ∀ p : ℕ, AddCommMonoid
      (BivariantClass delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)) :=
    fun i p ↦ (pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)).toAddCommMonoid
  { toFun := fun c i ↦
      DirectSum.mk
        (fun p : ℕ ↦ BivariantClass delta
          (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ))
        (c.2 i).toFinset
        (fun p ↦ ComponentRestriction.restrict delta f (p.1 : ℤ)
          (U i) (V (a i)) (h i) (c.1 p.1))
    map_zero' := by
      funext i
      apply DirectSum.ext
      intro p
      rw [directSum_mk_finite_apply]
      exact ComponentRestriction.restrict_zero delta f (p : ℤ) (U i) (V (a i)) (h i)
    map_add' := by
      intro c d
      funext i
      apply DirectSum.ext
      intro p
      simp only [Pi.add_apply, DirectSum.add_apply, directSum_mk_finite_apply]
      exact ComponentRestriction.restrict_add delta f (p : ℤ) (U i) (V (a i)) (h i)
        (c.1 p) (d.1 p) }

private theorem fromGlobal_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : Global delta f U V a h) (i : I) (p : ℕ) :
    fromGlobal delta f U V a h c i p =
      ComponentRestriction.restrict delta f (p : ℤ) (U i) (V (a i)) (h i) (c.1 p) := by
  -- Local instance justification (defeq pin): the DirectSum.mk expression in change must use the same degree monoids as fromGlobal and the component Nonnegative carrier.
  letI : ∀ q : ℕ, AddCommMonoid
      (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
        (q : ℤ)) :=
    fun q ↦ (pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (q : ℤ)).toAddCommMonoid
  change DirectSum.mk
    (fun q : ℕ ↦ BivariantClass delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (q : ℤ))
    (c.2 i).toFinset
    (fun q ↦ ComponentRestriction.restrict delta f (q.1 : ℤ)
      (U i) (V (a i)) (h i) (c.1 q.1)) p = _
  exact directSum_mk_finite_apply _ (c.2 i) p

/-- Completion is additively equivalent to componentwise-finite global families. -/
def globalEquiv
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Completion delta f U V a h ≃+ Global delta f U V a h :=
  { toFun := toGlobal delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
      hU_clopen hV_clopen h
    invFun := fromGlobal delta f U V a h
    left_inv := by
      intro c
      apply ext delta f U V a h
      intro i p
      -- Local instance justification (defeq pin): componentsEquiv.apply_symm_apply must use the global pointwise addition matching the assembled globalFamily.
      letI := pointwiseAddCommGroup delta f (p : ℤ)
      -- Local instance justification (defeq pin): componentsEquiv.apply_symm_apply must use the component product addition matching the restricted Nonnegative coefficients.
      letI : ∀ i, AddCommGroup
          (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
            (p : ℤ)) :=
        fun i ↦ pointwiseAddCommGroup delta
          (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
      rw [fromGlobal_apply]
      exact congrFun ((componentsEquiv delta f (p : ℤ) U V a hU_cover hV_cover
        hU_disjoint hV_disjoint hU_clopen hV_clopen h).apply_symm_apply
          (fun j ↦ c j p)) i
    right_inv := by
      intro c
      apply Subtype.ext
      funext p
      -- Local instance justification (defeq pin): componentsEquiv.injective must use the global pointwise addition matching the Global carrier in this degree.
      letI := pointwiseAddCommGroup delta f (p : ℤ)
      -- Local instance justification (defeq pin): componentsEquiv.apply_symm_apply must use the component product addition matching fromGlobal in this degree.
      letI : ∀ i, AddCommGroup
          (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i))
            (p : ℤ)) :=
        fun i ↦ pointwiseAddCommGroup delta
          (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
      apply (componentsEquiv delta f (p : ℤ) U V a hU_cover hV_cover hU_disjoint
        hV_disjoint hU_clopen hV_clopen h).injective
      funext i
      exact (congrFun ((componentsEquiv delta f (p : ℤ) U V a hU_cover hV_cover
        hU_disjoint hV_disjoint hU_clopen hV_clopen h).apply_symm_apply
          (fun j ↦ fromGlobal delta f U V a h c j p)) i).trans
            (fromGlobal_apply delta f U V a h c i p)
    map_add' := (toGlobal delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
      hU_clopen hV_clopen h).map_add' }

/-- The componentwise-to-global additive map is bijective. -/
theorem toGlobal_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Function.Bijective (toGlobal delta f U V a hU_cover hV_cover hU_disjoint
      hV_disjoint hU_clopen hV_clopen h) :=
  (globalEquiv delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
    hU_clopen hV_clopen h).bijective

/-- The forward global equivalence is the degreewise inverse-restriction family. -/
theorem globalEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : Completion delta f U V a h) (p : ℕ) :
    ((globalEquiv delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
      hU_clopen hV_clopen h).toEquiv.toFun c).1 p =
      globalFamily delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
        hU_clopen hV_clopen h c p := rfl

/-- The inverse global equivalence recovers coefficients by component restriction. -/
theorem globalEquiv_symm_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : Global delta f U V a h) (i : I) (p : ℕ) :
    (globalEquiv delta f U V a hU_cover hV_cover hU_disjoint hV_disjoint
      hU_clopen hV_clopen h).toEquiv.symm.toFun c i p =
      ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) (c.1 p) :=
  fromGlobal_apply delta f U V a h c i p

/-- Restriction in a fixed degree as an additive map to one selected component. -/
def degreeRestriction
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℕ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) (i : I) :=
  -- Local instance justification (defeq pin): the additive-map laws restrict_zero and restrict_add use the source pointwiseZero and pointwiseAdd.
  letI := pointwiseAddCommGroup delta f (p : ℤ)
  -- Local instance justification (defeq pin): the additive-map laws restrict_zero and restrict_add use the restricted component pointwiseZero and pointwiseAdd.
  letI := pointwiseAddCommGroup delta
    (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
  ({ toFun := fun c ↦ ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) c
     map_zero' := ComponentRestriction.restrict_zero delta f (p : ℤ)
       (U i) (V (a i)) (h i)
     map_add' := ComponentRestriction.restrict_add delta f (p : ℤ)
       (U i) (V (a i)) (h i) } :
    BivariantClass delta f (p : ℤ) →+
      BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ))

/-- Degreewise restriction from ordinary nonnegative classes to one component. -/
def completeComponent
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) (i : I) :
    BivariantClass.Nonnegative delta f →+
      BivariantClass.Nonnegative delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) :=
  -- Local instance justification (defeq pin): DirectSum.map must use the source degree monoids and zeros fixed by Nonnegative.
  letI : ∀ p : ℕ, AddCommMonoid (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta f (p : ℤ)).toAddCommMonoid
  -- Local instance justification (defeq pin): DirectSum.map must use the target degree monoids and zeros fixed by the restricted Nonnegative carrier.
  letI : ∀ p : ℕ, AddCommMonoid
      (BivariantClass delta
        (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)).toAddCommMonoid
  DirectSum.map fun p ↦ degreeRestriction delta f p U V a h i

/-- Complete an ordinary nonnegative bivariant class by restricting to every component. -/
def complete
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    BivariantClass.Nonnegative delta f →+ Completion delta f U V a h where
  toFun c i := completeComponent delta f U V a h i c
  map_zero' := by
    funext i
    exact (completeComponent delta f U V a h i).map_zero'
  map_add' := by
    intro c d
    funext i
    exact (completeComponent delta f U V a h i).map_add' c d

/-- Evaluation of completion is degreewise restriction to the selected component. -/
theorem complete_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : BivariantClass.Nonnegative delta f) (i : I) (p : ℕ) :
    complete delta f U V a h c i p =
      ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) (c p) := rfl

/-- Componentwise finite convolution composes two completed bivariant classes. -/
def comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    {I : Type v} {J : Type w} {K : Type x}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (W : K → Z.left.Opens)
    (a : I → J) (b : J → K)
    (hUV : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (hVW : ∀ j, V j ≤ g.left ⁻¹ᵁ W (b j))
    (hUW : ∀ i, U i ≤ (f ≫ g).left ⁻¹ᵁ W (b (a i)))
    (c : Completion delta f U V a hUV) (d : Completion delta g V W b hVW) :
    Completion delta (f ≫ g) U W (b ∘ a) hUW :=
  fun i ↦ BivariantClass.Nonnegative.castHom delta
    (ComponentRestriction.hom_comp f g (U i) (V (a i)) (W (b (a i)))
      (hUV i) (hVW (a i)) (hUW i))
    (BivariantClass.Nonnegative.comp delta
      (ComponentRestriction.hom f (U i) (V (a i)) (hUV i))
      (ComponentRestriction.hom g (V (a i)) (W (b (a i))) (hVW (a i))) (c i) (d (a i)))

/-- Completed composition is the transported finite convolution on each component. -/
theorem comp_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    {I : Type v} {J : Type w} {K : Type x}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (W : K → Z.left.Opens)
    (a : I → J) (b : J → K)
    (hUV : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (hVW : ∀ j, V j ≤ g.left ⁻¹ᵁ W (b j))
    (hUW : ∀ i, U i ≤ (f ≫ g).left ⁻¹ᵁ W (b (a i)))
    (c : Completion delta f U V a hUV) (d : Completion delta g V W b hVW) (i : I) :
    comp delta f g U V W a b hUV hVW hUW c d i =
      BivariantClass.Nonnegative.castHom delta
        (ComponentRestriction.hom_comp f g (U i) (V (a i)) (W (b (a i)))
          (hUV i) (hVW (a i)) (hUW i))
        (BivariantClass.Nonnegative.comp delta
          (ComponentRestriction.hom f (U i) (V (a i)) (hUV i))
          (ComponentRestriction.hom g (V (a i)) (W (b (a i))) (hVW (a i)))
          (c i) (d (a i))) := rfl

/-- Completion carries ordinary composition to componentwise completed composition. -/
theorem complete_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    {I : Type v} {J : Type w} {K : Type x}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (W : K → Z.left.Opens)
    (a : I → J) (b : J → K)
    (hUV : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (hVW : ∀ j, V j ≤ g.left ⁻¹ᵁ W (b j))
    (hUW : ∀ i, U i ≤ (f ≫ g).left ⁻¹ᵁ W (b (a i)))
    (c : BivariantClass.Nonnegative delta f)
    (d : BivariantClass.Nonnegative delta g) :
    complete delta (f ≫ g) U W (b ∘ a) hUW
        (BivariantClass.Nonnegative.comp delta f g c d) =
      comp delta f g U V W a b hUV hVW hUW
        (complete delta f U V a hUV c) (complete delta g V W b hVW d) := sorry

end Completion

end AlgebraicGeometry.BivariantClass.OpenRestriction
