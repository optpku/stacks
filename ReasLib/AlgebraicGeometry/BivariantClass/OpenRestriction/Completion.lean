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
        (ComponentRestriction.hom f (U i) (V (a i)) (h i))) := sorry

/-- Two completed classes are equal when all homogeneous component values agree. -/
@[ext]
theorem ext
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    {c d : Completion delta f U V a h} (heq : ∀ i p, c i p = d i p) : c = d := sorry

/-- Global nonnegative families whose restriction to each source component is nonzero in
only finitely many degrees. -/
def componentwiseFiniteSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :=
  -- Local instance justification (defeq pin): use the explicit pointwise groups.
  letI : ∀ p : ℕ, AddCommGroup (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ pointwiseAddCommGroup delta f (p : ℤ)
  ({ carrier := {c | ∀ i, {p : ℕ | ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) (c p) ≠
          pointwiseZero delta
            (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite}
     zero_mem' := sorry
     add_mem' := sorry
     neg_mem' := sorry } : AddSubgroup (∀ p : ℕ, BivariantClass delta f (p : ℤ)))

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
            (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)}.Finite := sorry

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
  -- Local instance justification (defeq pin): the equivalence uses the explicit source group.
  letI := pointwiseAddCommGroup delta f p
  -- Local instance justification (defeq pin): the target product uses explicit component groups.
  letI : ∀ i, AddCommGroup
      (BivariantClass delta (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p) :=
    fun i ↦ pointwiseAddCommGroup delta
      (ComponentRestriction.hom f (U i) (V (a i)) (h i)) p
  { toFun := ComponentRestriction.components delta f p U V a h
    invFun := ComponentRestriction.assemble delta f p U V a hU_cover hV_cover
      hU_disjoint hV_disjoint hU_clopen hV_clopen h
    left_inv := sorry
    right_inv := sorry
    map_add' := sorry }

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
      hU_clopen hV_clopen h c ∈ componentwiseFiniteSubgroup delta f U V a h := sorry

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
  map_zero' := sorry
  map_add' := sorry

/-- Restrict a componentwise-finite global family degreewise to every source component. -/
def fromGlobal
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Global delta f U V a h →+ Completion delta f U V a h :=
  -- Local instance justification (defeq pin): each direct-sum target uses its explicit componentwise additive family.
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
    map_zero' := sorry
    map_add' := sorry }

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
    left_inv := sorry
    right_inv := sorry
    map_add' := sorry }

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
      hV_disjoint hU_clopen hV_clopen h) := sorry

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
        hU_clopen hV_clopen h c p := sorry

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
        (U i) (V (a i)) (h i) (c.1 p) := sorry

/-- Restriction in a fixed degree as an additive map to one selected component. -/
def degreeRestriction
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℕ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) (i : I) :=
  -- Local instance justification (defeq pin): the source additive structure is explicit.
  letI := pointwiseAddCommGroup delta f (p : ℤ)
  -- Local instance justification (defeq pin): the component additive structure is explicit.
  letI := pointwiseAddCommGroup delta
    (ComponentRestriction.hom f (U i) (V (a i)) (h i)) (p : ℤ)
  ({ toFun := fun c ↦ ComponentRestriction.restrict delta f (p : ℤ)
        (U i) (V (a i)) (h i) c
     map_zero' := sorry
     map_add' := sorry } :
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
  -- Local instance justification (defeq pin): the source direct sum uses its explicit additive family.
  letI : ∀ p : ℕ, AddCommMonoid (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta f (p : ℤ)).toAddCommMonoid
  -- Local instance justification (defeq pin): the restricted direct sum uses its explicit additive family.
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
  map_zero' := sorry
  map_add' := sorry

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
        (U i) (V (a i)) (h i) (c p) := sorry

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
          (c i) (d (a i))) := sorry

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
