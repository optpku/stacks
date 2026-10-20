module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.AcyclicReduction
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.HomotopyExtension
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.HomotopyGluing
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-! # Nullhomotopies along an acyclic reduction tower

The successor extension and the limit descent define sections of the presheaf of
nullhomotopies on a reduction tower. Native well-order recursion constructs a compatible
section, whose value at the exhaustion stage gives a homotopy on the ambient complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe z w v u

namespace CochainComplex.AcyclicReduction

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {M I : CochainComplex C ℤ} {κ : Cardinal.{z}}

/-- Restrict a nullhomotopy to an earlier stage of the reduction. -/
def restrictNullHomotopy (R : AcyclicReduction M κ) (f : M ⟶ I)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (h : Homotopy ((R.stage β).arrow ≫ f) 0) :
    Homotopy ((R.stage α).arrow ≫ f) 0 :=
  (Homotopy.ofEq (by rw [← Category.assoc, Subobject.ofLE_arrow])).trans
    ((h.compLeft (Subobject.ofLE _ _ (R.monotone hαβ))).trans
      (Homotopy.ofEq Limits.comp_zero))

/-- Restriction acts on homotopy components by the actual stage inclusion. -/
@[simp]
lemma restrictNullHomotopy_hom (R : AcyclicReduction M κ) (f : M ⟶ I)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (h : Homotopy ((R.stage β).arrow ≫ f) 0)
    (p q : ℤ) :
    (R.restrictNullHomotopy f hαβ h).hom p q =
      (Subobject.ofLE _ _ (R.monotone hαβ)).f p ≫ h.hom p q := by
  simp [restrictNullHomotopy]

/-- Nullhomotopies on stages, with restriction along their inclusions. -/
def nullHomotopyFunctor (R : AcyclicReduction M κ) (f : M ⟶ I) :
    Ordinal.{w}ᵒᵖ ⥤ Type v where
  obj α := Homotopy ((R.stage α.unop).arrow ≫ f) 0
  map φ := ↾fun h ↦ R.restrictNullHomotopy f (leOfHom φ.unop) h
  map_id := by
    intro α
    ext h p q
    simp
  map_comp := by
    intro α β γ φ ψ
    ext h p q
    change (R.restrictNullHomotopy f (leOfHom (φ ≫ ψ).unop) h).hom p q =
      (R.restrictNullHomotopy f (leOfHom ψ.unop)
        (R.restrictNullHomotopy f (leOfHom φ.unop) h)).hom p q
    simp only [restrictNullHomotopy_hom]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_comp_ofLE]

variable [∀ n : ℤ, Injective (I.X n)]

/-- Extend a stage nullhomotopy across the actual successor short exact sequence.
At an exhausted stage the inverse of the stage-equality isomorphism gives the extension. -/
def successorNullHomotopy (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0)
    (f : M ⟶ I) (β : Ordinal.{w}) (h : Homotopy ((R.stage β).arrow ≫ f) 0) :
    Homotopy ((R.stage (Order.succ β)).arrow ≫ f) 0 := by
  classical
  by_cases htop : R.stage β = ⊤
  · let e := Subobject.isoOfEq (R.stage (Order.succ β)) (R.stage β)
      (R.stage_succ_of_eq_top β htop)
    exact (Homotopy.ofEq (by sorry)).trans
      ((h.compLeft e.hom).trans (Homotopy.ofEq Limits.comp_zero))
  · let hs : Homotopy ((R.successor β).f ≫ ((R.stage (Order.succ β)).arrow ≫ f)) 0 :=
      (Homotopy.ofEq (by rw [← Category.assoc, Subobject.ofLE_arrow])).trans h
    exact HomotopyExtension.extend (R.shortExact β) _ hs
      (kill (R.quotient β) (R.quotient_boundedBy β htop)
        (HomotopyExtension.quotientMap (R.shortExact β) _ hs))

/-- Successor extension retains the previously specified homotopy components. -/
lemma restrict_successorNullHomotopy (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0)
    (f : M ⟶ I) (β : Ordinal.{w}) (h : Homotopy ((R.stage β).arrow ≫ f) 0) :
    R.restrictNullHomotopy f (Order.le_succ β) (R.successorNullHomotopy kill f β h) = h := by
  sorry

/-- The stage homotopy supplied by a compatible section below a limit ordinal. -/
def limitStageNullHomotopy (R : AcyclicReduction M κ) (f : M ⟶ I)
    (α : Ordinal.{w})
    (s : ((OrderHom.Subtype.val (· ∈ Set.Iio α)).monotone.functor.op ⋙
      R.nullHomotopyFunctor f).sections) (j : α.ToType) :
    Homotopy ((limitCocone R.stage R.monotone α).ι.app j ≫
      ((R.stage α).arrow ≫ f)) 0 :=
  (Homotopy.ofEq (show (limitCocone R.stage R.monotone α).ι.app j ≫
      ((R.stage α).arrow ≫ f) = (R.stage (j : Ordinal)).arrow ≫ f from by
    change Subobject.ofLE _ _ (R.monotone j.toOrd.2.le) ≫
      ((R.stage α).arrow ≫ f) = (R.stage (j : Ordinal)).arrow ≫ f
    rw [← Category.assoc, Subobject.ofLE_arrow])).trans
    (s.val (op ⟨j, j.toOrd.2⟩))

/-- A compatible section gives strictly compatible components on the small limit diagram. -/
lemma limitStageNullHomotopy_compatible (R : AcyclicReduction M κ) (f : M ⟶ I)
    (α : Ordinal.{w})
    (s : ((OrderHom.Subtype.val (· ∈ Set.Iio α)).monotone.functor.op ⋙
      R.nullHomotopyFunctor f).sections)
    {j j' : α.ToType} (φ : j ⟶ j') (p q : ℤ) :
    ((limitFunctor R.stage R.monotone α).map φ).f p ≫
        (R.limitStageNullHomotopy f α s j').hom p q =
      (R.limitStageNullHomotopy f α s j).hom p q := by
  sorry

/-- Glue the specified compatible stage homotopies by degreewise colimit descent. -/
def limitNullHomotopy (R : AcyclicReduction M κ) (f : M ⟶ I)
    (α : Ordinal.{w}) (hα : Order.IsSuccLimit α)
    (s : ((OrderHom.Subtype.val (· ∈ Set.Iio α)).monotone.functor.op ⋙
      R.nullHomotopyFunctor f).sections) :
    Homotopy ((R.stage α).arrow ≫ f) 0 :=
  Homotopy.glueNullHomotopy
    (fun n ↦ isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
      (R.isColimit α hα))
    (R.limitStageNullHomotopy f α s)
    (fun _ _ φ p q ↦ R.limitStageNullHomotopy_compatible f α s φ p q)

/-- The limit descent restricts to the given section at every earlier ordinal. -/
lemma restrict_limitNullHomotopy (R : AcyclicReduction M κ) (f : M ⟶ I)
    (α : Ordinal.{w}) (hα : Order.IsSuccLimit α)
    (s : ((OrderHom.Subtype.val (· ∈ Set.Iio α)).monotone.functor.op ⋙
      R.nullHomotopyFunctor f).sections) (β : Ordinal.{w}) (hβ : β < α) :
    R.restrictNullHomotopy f hβ.le (R.limitNullHomotopy f α hα s) =
      s.val (op ⟨β, hβ⟩) := by
  sorry

/-- Explicit successor extension and limit gluing are the input to native well-order recursion. -/
def nullHomotopyInduction (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0) (f : M ⟶ I) :
    (R.nullHomotopyFunctor f).WellOrderInductionData where
  succ β _ h := R.successorNullHomotopy kill f β h
  map_succ β _ h := R.restrict_successorNullHomotopy kill f β h
  lift α hα s := R.limitNullHomotopy f α hα s
  map_lift α hα s β hβ := R.restrict_limitNullHomotopy f α hα s β hβ

/-- The homotopy at the zero stage has zero components. -/
def zeroNullHomotopy (R : AcyclicReduction M κ) (f : M ⟶ I) :
    Homotopy ((R.stage 0).arrow ≫ f) 0 :=
  Homotopy.ofEq (by sorry)

/-- Native well-order recursion constructs a compatible nullhomotopy on every stage. -/
def nullHomotopySection (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0) (f : M ⟶ I) :
    (R.nullHomotopyFunctor f).sections :=
  (R.nullHomotopyInduction kill f).sectionsMk (R.zeroNullHomotopy f)

/-- Evaluate the compatible section at the exhaustion stage and pull back along its actual
inverse to obtain a nullhomotopy on the whole ambient complex. -/
@[stacks 079L "nullhomotopy from an actual acyclic reduction"]
def nullHomotopy (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0) (f : M ⟶ I) : Homotopy f 0 :=
  (Homotopy.ofEq (show f = R.exhaustionIso.inv ≫
      ((R.stage R.exhaustion).arrow ≫ f) from by
    rw [← R.exhaustionIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp])).trans
    ((((R.nullHomotopySection kill f).val (op R.exhaustion)).compLeft
      R.exhaustionIso.inv).trans (Homotopy.ofEq Limits.comp_zero))

/-- Each final component is the exhaustion inverse followed by the recursively constructed
component on that stage. -/
@[simp]
lemma nullHomotopy_hom (R : AcyclicReduction M κ)
    (kill : ∀ (N : CochainComplex C ℤ), SmallAcyclic.BoundedBy κ N →
      (g : N ⟶ I) → Homotopy g 0) (f : M ⟶ I) (p q : ℤ) :
    (R.nullHomotopy kill f).hom p q = R.exhaustionIso.inv.f p ≫
      ((R.nullHomotopySection kill f).val (op R.exhaustion)).hom p q := by
  simp [nullHomotopy]

end CochainComplex.AcyclicReduction
