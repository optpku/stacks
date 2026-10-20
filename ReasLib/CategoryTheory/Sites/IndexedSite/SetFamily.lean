module

public import Mathlib.SetTheory.ZFC.Ordinal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Families of arrows indexed by sets

These families retain an actual set of indices, together with a set-theoretic encoding of
their target and indexed arrows. Composition uses ordered pairs of the original indices.
-/

@[expose] public section

universe w v u

noncomputable section

namespace CategoryTheory

/-- A family of arrows with a common target and an actual set of indices. -/
structure SetIndexedFamily {C : Type u} [Category.{v} C] (target : C) where
  indexSet : ZFSet.{max u v w}
  X : Shrink.{max u v w} indexSet → C
  f : ∀ i, X i ⟶ target

namespace SetIndexedFamily

variable {C : Type u} [Category.{v} C] {target : C}

/-- The small type of elements of the index set of a family. -/
abbrev index (F : SetIndexedFamily.{w} target) : Type (max u v w) :=
  Shrink.{max u v w} F.indexSet

/-- The set element represented by an index of a family. -/
def indexVal (F : SetIndexedFamily.{w} target) (i : F.index) : ZFSet.{max u v w} :=
  ((equivShrink F.indexSet).symm i).val

/-- Construct a set-indexed family from its objects and arrows. -/
def ofArrows (indexSet : ZFSet.{max u v w})
    (X : Shrink.{max u v w} indexSet → C) (f : ∀ i, X i ⟶ target) :
    SetIndexedFamily.{w} target :=
  ⟨indexSet, X, f⟩

/-- View a set-indexed family as an indexed family in the slice over its target. -/
def toFamily (F : SetIndexedFamily.{w} target) :
    SemiRepresentableFamily.Over.{max u v w} target :=
  SemiRepresentableFamily.Over.ofArrows F.X F.f

/-- The singleton family of an arrow, indexed by the set containing the empty set. -/
def singleton {source : C} (f : source ⟶ target) : SetIndexedFamily.{w} target :=
  ofArrows {∅} (fun _ => source) (fun _ => f)

/-- The ordered-pair index set for composing a family with families over its members. -/
def bindIndexSet (F : SetIndexedFamily.{w} target)
    (G : ∀ i : F.index, SetIndexedFamily.{w} (F.X i)) : ZFSet.{max u v w} :=
  ZFSet.range (fun ij : Σ i : F.index, (G i).index =>
    ZFSet.pair (F.indexVal ij.1) ((G ij.1).indexVal ij.2))

/-- Dependent pairs of indices correspond to elements of the composition index set. -/
def bindIndexEquiv (F : SetIndexedFamily.{w} target)
    (G : ∀ i : F.index, SetIndexedFamily.{w} (F.X i)) :
    (Σ i : F.index, (G i).index) ≃ Shrink.{max u v w} (F.bindIndexSet G) := by
  let pairMap : (Σ i : F.index, (G i).index) → F.bindIndexSet G :=
    fun ij => ⟨ZFSet.pair (F.indexVal ij.1) ((G ij.1).indexVal ij.2),
      ZFSet.mem_range_self ij⟩
  refine (Equiv.ofBijective pairMap ⟨?_, ?_⟩).trans (equivShrink (F.bindIndexSet G))
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hp := ZFSet.pair_inj.mp (congrArg Subtype.val h)
    have hi : i = i' := (equivShrink F.indexSet).symm.injective
      (Subtype.ext hp.1)
    subst i'
    have hj : j = j' := (equivShrink (G i).indexSet).symm.injective
      (Subtype.ext hp.2)
    subst j'
    rfl
  · rintro ⟨z, hz⟩
    obtain ⟨ij, hij⟩ := ZFSet.mem_range.mp hz
    exact ⟨ij, Subtype.ext hij⟩

/-- Compose the arrows of a family with the arrows of its refinements. -/
def bind (F : SetIndexedFamily.{w} target)
    (G : ∀ i : F.index, SetIndexedFamily.{w} (F.X i)) : SetIndexedFamily.{w} target :=
  ofArrows (F.bindIndexSet G)
    (fun k => (G ((F.bindIndexEquiv G).symm k).1).X ((F.bindIndexEquiv G).symm k).2)
    (fun k => (G ((F.bindIndexEquiv G).symm k).1).f ((F.bindIndexEquiv G).symm k).2 ≫
      F.f ((F.bindIndexEquiv G).symm k).1)

/-- A set encoding of the target, actual index set, and indexed graph of arrows of a family. -/
def code (F : SetIndexedFamily.{w} target) : ZFSet.{max u v w} :=
  ZFSet.pair
    (Ordinal.toZFSet (Ordinal.lift.{max u v w}
      (Ordinal.typein (WellOrderingRel : C → C → Prop) target)))
    (ZFSet.pair F.indexSet (ZFSet.range (fun i : F.index =>
      ZFSet.pair (F.indexVal i)
        (Ordinal.toZFSet (Ordinal.lift.{max u v w}
          (Ordinal.typein
            (WellOrderingRel : (Σ A : C, Σ B : C, A ⟶ B) →
              (Σ A : C, Σ B : C, A ⟶ B) → Prop)
            ⟨F.X i, target, F.f i⟩))))))

/-- The set encoding distinguishes complete families, including their targets and indices. -/
theorem code_injective :
    Function.Injective (fun F : Σ target : C, SetIndexedFamily.{w} target => F.2.code) :=
  sorry

/-- A collection of set-indexed families is a site when singleton isomorphisms cover,
composites of coverings cover, and covering families admit covering pullbacks. -/
def IsSite (Cov : ∀ target : C, Set (SetIndexedFamily.{w} target)) : Prop :=
  (∀ {source target : C} (f : source ⟶ target) [IsIso f], singleton f ∈ Cov target) ∧
    (∀ {target : C} (F : SetIndexedFamily.{w} target), F ∈ Cov target →
      ∀ (G : ∀ i : F.index, SetIndexedFamily.{w} (F.X i)),
        (∀ i, G i ∈ Cov (F.X i)) → F.bind G ∈ Cov target) ∧
    (∀ {target target' : C} (F : SetIndexedFamily.{w} target), F ∈ Cov target →
      ∀ (base : target' ⟶ target),
        ∃ (P : F.index → C) (first : ∀ i, P i ⟶ target')
          (second : ∀ i, P i ⟶ F.X i),
          (∀ i, IsPullback (first i) (second i) base (F.f i)) ∧
            ofArrows F.indexSet P first ∈ Cov target')

end SetIndexedFamily

end CategoryTheory
