module

public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Reindex
public import Mathlib.Algebra.DirectSum.Ring

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The grading identity used by composition of cap operations. -/
theorem compDegree (k p q : ℤ) : (k - q) - p = k - (p + q) := sorry

/-- The comparison map into the pullback used to compose two cap operations commutes. -/
theorem compLift_comm
    {S : Scheme.{u}} {X Y Z X' Z' : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) :
    fg'.left ≫ h.left = (i ≫ f).left ≫ g.left := sorry

/-- The underlying comparison map from a square for `f ≫ g` to the pullback of `g`. -/
def compLiftLeft
    {S : Scheme.{u}} {X Y Z X' Z' : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) :
    X'.left ⟶ (ComponentRestriction.baseChange g h).left :=
  pullback.lift fg'.left (i ≫ f).left (compLift_comm f g i fg' h square)

/-- The comparison map for composition respects the maps to the base scheme. -/
theorem compLift_over
    {S : Scheme.{u}} {X Y Z X' Z' : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) :
    compLiftLeft f g i fg' h square ≫ (ComponentRestriction.baseChange g h).hom =
      X'.hom := sorry

/-- The comparison from a square for `f ≫ g` to the canonical pullback of `g`. -/
def compLift
    {S : Scheme.{u}} {X Y Z X' Z' : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) :
    X' ⟶ ComponentRestriction.baseChange g h :=
  Over.homMk (compLiftLeft f g i fg' h square) (compLift_over f g i fg' h square)

/-- The source projection from a locally finite-type base change is locally of finite type. -/
theorem locallyOfFiniteTypeBaseChangeToSource
    {S : Scheme.{u}} {Y Z Z' : Over S} (g : Y ⟶ Z) (h : Z' ⟶ Z)
    [LocallyOfFiniteType h.left] :
    LocallyOfFiniteType (ComponentRestriction.baseChangeToSource g h).left :=
  MorphismProperty.pullback_snd h.left g.left inferInstance

/-- The comparison square used by the first cap operation in a composite is cartesian. -/
theorem compLift_isPullback
    {S : Scheme.{u}} {X Y Z X' Z' : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z)
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) :
    IsPullback i.left (compLift f g i fg' h square).left f.left
      (ComponentRestriction.baseChangeToSource g h).left := sorry

/-- The cap family obtained by first applying a class for `g` and then one for `f`. -/
def compCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q) :
    CapFamily delta (f ≫ g) (p + q) :=
  fun {X' Z'} _ _ i fg' h _ square k ↦
    -- Local instance justification (proof-local temporary data): both cap maps require this finite-type proof for the base-change object.
    letI := ComponentRestriction.locallyOfFiniteTypeBaseChange g h
    -- Local instance justification (proof-local temporary data): the first cap map requires this finite-type proof for the base-change projection.
    letI := locallyOfFiniteTypeBaseChangeToSource g h
    (RelativeChow.castDegree delta (compDegree k p q)).comp
      ((c.cap i (compLift f g i fg' h square)
        (ComponentRestriction.baseChangeToSource g h)
        (compLift_isPullback f g i fg' h square) (k - q)).comp
      (d.cap (ComponentRestriction.baseChangeToSource g h)
        (ComponentRestriction.baseChangeToTarget g h) h
        (ComponentRestriction.baseChange_isPullback g h) k))

/-- Composed cap families preserve proper pushforward. -/
theorem compCap_map_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q) :
    CompatibleWithProperPushforward delta (compCap delta f g c d) := sorry

/-- Composed cap families preserve flat pullback. -/
theorem compCap_pullback_flat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q) :
    CompatibleWithFlatPullback delta (compCap delta f g c d) := sorry

/-- Composed cap families preserve effective-Cartier Gysin pullback. -/
theorem compCap_gysin_cartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q) :
    CompatibleWithCartierGysin delta (compCap delta f g c d) := sorry

/-- Homogeneous composition of bivariant classes on composable morphisms. -/
def comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q) :
    BivariantClass delta (f ≫ g) (p + q) where
  cap := compCap delta f g c d
  map_proper := compCap_map_proper delta f g c d
  pullback_flat := compCap_pullback_flat delta f g c d
  gysin_cartier := compCap_gysin_cartier delta f g c d

/-- Homogeneous composition acts by the explicitly composed cap family. -/
theorem comp_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d : BivariantClass delta g q)
    {X' Z' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Z'.hom]
    (i : X' ⟶ X) (fg' : X' ⟶ Z') (h : Z' ⟶ Z) [LocallyOfFiniteType h.left]
    (square : IsPullback i.left fg'.left (f ≫ g).left h.left) (k : ℤ) :
    (comp delta f g c d).cap i fg' h square k =
      compCap delta f g c d i fg' h square k := sorry

/-- Homogeneous composition preserves pointwise addition in its first variable. -/
theorem add_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c c' : BivariantClass delta f p) (d : BivariantClass delta g q) :
    comp delta f g (pointwiseAdd delta f p c c') d =
      pointwiseAdd delta (f ≫ g) (p + q) (comp delta f g c d) (comp delta f g c' d) := sorry

/-- Homogeneous composition preserves pointwise addition in its second variable. -/
theorem comp_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) {p q : ℤ}
    (c : BivariantClass delta f p) (d d' : BivariantClass delta g q) :
    comp delta f g c (pointwiseAdd delta g q d d') =
      pointwiseAdd delta (f ≫ g) (p + q) (comp delta f g c d) (comp delta f g c d') := sorry

/-- Homogeneous composition of pointwise-zero classes is pointwise zero. -/
theorem zero_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) (p q : ℤ) :
    comp delta f g (pointwiseZero delta f p) (pointwiseZero delta g q) =
      pointwiseZero delta (f ≫ g) (p + q) := sorry

/-- The nonnegative graded bivariant classes on a morphism. -/
abbrev Nonnegative
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) : Type (u + 1) :=
  @DirectSum ℕ (fun p ↦ BivariantClass delta f (p : ℤ))
    (fun p ↦ (pointwiseAddCommGroup delta f (p : ℤ)).toAddCommMonoid)

/-- The nonnegative carrier is the direct sum of its homogeneous degrees. -/
theorem nonnegative_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) :
    Nonnegative delta f =
      @DirectSum ℕ (fun p ↦ BivariantClass delta f (p : ℤ))
        (fun p ↦ (pointwiseAddCommGroup delta f (p : ℤ)).toAddCommMonoid) := sorry

namespace Nonnegative

/-- Homogeneous bivariant composition as a biadditive map in fixed degrees. -/
def homogeneousComp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) (p q : ℕ) :=
  -- Local instance justification (defeq pin): use the explicit source pointwise group.
  letI := pointwiseAddCommGroup delta f (p : ℤ)
  -- Local instance justification (defeq pin): this fixes the second explicit pointwise group.
  letI := pointwiseAddCommGroup delta g (q : ℤ)
  -- Local instance justification (defeq pin): this fixes the target explicit pointwise group.
  letI := pointwiseAddCommGroup delta (f ≫ g) (p + q : ℕ)
  ({ toFun := fun c ↦
      { toFun := fun d ↦ comp delta f g c d
        map_zero' := sorry
        map_add' := sorry }
     map_zero' := sorry
     map_add' := sorry } :
    BivariantClass delta f (p : ℤ) →+
      BivariantClass delta g (q : ℤ) →+
        BivariantClass delta (f ≫ g) (p + q : ℕ))

/-- Finite convolution of nonnegative graded bivariant classes as a biadditive map. -/
def compHom
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonnegative delta f →+ Nonnegative delta g →+ Nonnegative delta (f ≫ g) :=
  -- Local instance justification (defeq pin): the first direct sum uses the explicit source additive family.
  letI : ∀ n : ℕ, AddCommMonoid (BivariantClass delta f (n : ℤ)) :=
    fun n ↦ (pointwiseAddCommGroup delta f (n : ℤ)).toAddCommMonoid
  -- Local instance justification (defeq pin): the second direct sum uses the explicit source additive family.
  letI : ∀ n : ℕ, AddCommMonoid (BivariantClass delta g (n : ℤ)) :=
    fun n ↦ (pointwiseAddCommGroup delta g (n : ℤ)).toAddCommMonoid
  -- Local instance justification (defeq pin): the target direct sum uses the explicit composite additive family.
  letI : ∀ n : ℕ, AddCommMonoid (BivariantClass delta (f ≫ g) (n : ℤ)) :=
    fun n ↦ (pointwiseAddCommGroup delta (f ≫ g) (n : ℤ)).toAddCommMonoid
  DirectSum.toAddMonoid fun p ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun q ↦
      AddMonoidHom.flip <|
        (DirectSum.of (fun n : ℕ ↦ BivariantClass delta (f ≫ g) (n : ℤ)) (p + q)).compHom.comp
          (homogeneousComp delta f g p q)

/-- Finite antidiagonal convolution of nonnegative graded bivariant classes. -/
def comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Nonnegative delta f) (d : Nonnegative delta g) : Nonnegative delta (f ≫ g) :=
  compHom delta f g c d

/-- Transport a bivariant class along equality of its grading index. -/
def castGrading
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p q : ℤ} (e : p = q) :=
  -- Local instance justification (defeq pin): the source pointwise group is supplied explicitly.
  letI := pointwiseAddCommGroup delta f p
  -- Local instance justification (defeq pin): the target pointwise group is supplied explicitly.
  letI := pointwiseAddCommGroup delta f q
  ({ toFun := fun c ↦ e ▸ c
     map_zero' := sorry
     map_add' := sorry } : BivariantClass delta f p →+ BivariantClass delta f q)

/-- A pair in the `n`th antidiagonal has total integer degree `n`. -/
theorem antidiagonalDegree (n : ℕ) (ij : Finset.antidiagonal n) :
    (ij.1.1 : ℤ) + (ij.1.2 : ℤ) = (n : ℤ) := sorry

/-- The explicit finite antidiagonal coefficient of nonnegative composition. -/
def coefficient
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Nonnegative delta f) (d : Nonnegative delta g) (n : ℕ) :
    BivariantClass delta (f ≫ g) (n : ℤ) :=
  -- Local instance justification (defeq pin): the finite sum uses the explicit target group.
  letI := pointwiseAddCommGroup delta (f ≫ g) (n : ℤ)
  ∑ ij : Finset.antidiagonal n,
    castGrading delta (antidiagonalDegree n ij)
      (BivariantClass.comp delta f g (c ij.1.1) (d ij.1.2))

/-- Degree `n` of nonnegative composition is its finite antidiagonal convolution. -/
theorem comp_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Nonnegative delta f) (d : Nonnegative delta g) (n : ℕ) :
    comp delta f g c d n = coefficient delta f g c d n := sorry

/-- Transport nonnegative graded bivariant classes along equality of morphisms. -/
def castHom
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f f' : X ⟶ Y} (e : f = f') : Nonnegative delta f →+ Nonnegative delta f' :=
  -- Local instance justification (defeq pin): the source direct sum uses its explicit additive family.
  letI : ∀ p : ℕ, AddCommMonoid (BivariantClass delta f (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta f (p : ℤ)).toAddCommMonoid
  -- Local instance justification (defeq pin): the target direct sum uses its explicit additive family.
  letI : ∀ p : ℕ, AddCommMonoid (BivariantClass delta f' (p : ℤ)) :=
    fun p ↦ (pointwiseAddCommGroup delta f' (p : ℤ)).toAddCommMonoid
  DirectSum.map fun p ↦
    -- Local instance justification (defeq pin): the source pointwise group is explicit.
    letI := pointwiseAddCommGroup delta f (p : ℤ)
    -- Local instance justification (defeq pin): the transported pointwise group is explicit.
    letI := pointwiseAddCommGroup delta f' (p : ℤ)
    ({ toFun := fun c ↦ e ▸ c
       map_zero' := sorry
       map_add' := sorry } :
      BivariantClass delta f (p : ℤ) →+ BivariantClass delta f' (p : ℤ))

end Nonnegative

end AlgebraicGeometry.BivariantClass
