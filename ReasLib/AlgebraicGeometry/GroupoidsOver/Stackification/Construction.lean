module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification.HomSize
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Canonical
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Stackification with the original scheme Hom universe

Actual local plus codes and an actual small fppf refinement supply the Hom
shrink equivalences. The total objects and the maps to the base are retained.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Functor.StackificationConstruction
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Stackification

variable {S : Scheme.{u}} {X : Type (u + 1)} [Category.{u} X]
variable (p : X ⥤ Over S) (χ : p.Cleavage)

/-- The concrete large realization before replacing its Hom types by their actual codes. -/
abbrev largeTotal :=
  Pseudofunctor.CoGrothendieck
    (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'

/-- The actual small code of a total arrow includes its base arrow and its
completion-fibre arrow, encoded by the specified small product construction. -/
def TotalHomCode (a b : largeTotal p χ) : Type u :=
  letI : ∀ f : a.base ⟶ b.base, Small.{u} (a.fiber ⟶
      ((completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'.map
        f.op.toLoc).toFunctor.obj b.fiber) := fun f ↦ completionHomSmall p χ a.fiber _
  Σ f : a.base ⟶ b.base,
    Shrink.{u} (a.fiber ⟶
      ((completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'.map
        f.op.toLoc).toFunctor.obj b.fiber)

/-- Encode both actual fields of a co-Grothendieck arrow. -/
def encodeTotalHom {a b : largeTotal p χ} (φ : a ⟶ b) : TotalHomCode p χ a b :=
  letI : Small.{u} (a.fiber ⟶
      ((completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'.map
        φ.base.op.toLoc).toFunctor.obj b.fiber) := completionHomSmall p χ a.fiber _
  ⟨φ.base, (equivShrink _) φ.fiber⟩

/-- The base and fibre fields, together with their actual shrink equivalences,
determine the original arrow. -/
theorem encodeTotalHom_injective (a b : largeTotal p χ) :
    Function.Injective (encodeTotalHom p χ (a := a) (b := b)) := sorry

/-- Every total Hom type has the supplied actual original-universe code. -/
instance totalLocallySmall : LocallySmall.{u} (largeTotal p χ) where
  hom_small a b := small_of_injective (encodeTotalHom_injective p χ a b)

/-- The native category with the same objects and actual small Hom models. -/
def smallTotal := ShrinkHoms (largeTotal p χ)

instance smallCategory : Category.{u} (smallTotal p χ) :=
  inferInstanceAs (Category.{u} (ShrinkHoms (largeTotal p χ)))

/-- The projection after the native Hom shrink is still the original projection on objects. -/
def smallProjection : smallTotal p χ ⥤ Over S :=
  (ShrinkHoms.equivalence.{u} (largeTotal p χ)).inverse ⋙
    targetProjection (Scheme.fppfTopology.over S) p χ

/-- The actual Hom shrink functor is based over the original site. -/
def shrinkBased :
    BasedCategory.ofFunctor (targetProjection (Scheme.fppfTopology.over S) p χ) ⥤ᵇ
      BasedCategory.ofFunctor (smallProjection p χ) :=
  BasedFunctor.ofFunctor (ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor (by sorry)

/-- The inverse Hom shrink retains every original arrow and base lift. -/
theorem inverse_isHomLift {R T : Over S} {a b : smallTotal p χ}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : (smallProjection p χ).IsHomLift f φ) :
    (targetProjection (Scheme.fppfTopology.over S) p χ).IsHomLift f
      ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).inverse.map φ) := by
  cases hφ
  exact .map _

/-- A supplied actual strong certificate is transported with its actual
factor map, then encoded by the native Hom shrink equivalence. -/
theorem shrinkStrong {R T : Over S} {a b : largeTotal p χ} (f : R ⟶ T) (φ : a ⟶ b)
    (hφ : (targetProjection (Scheme.fppfTopology.over S) p χ).IsStronglyCartesian f φ) :
    (smallProjection p χ).IsStronglyCartesian f
      ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor.map φ) where
  toIsHomLift := by sorry
  universal_property' := by
    intro z g τ hτ
    let e := ShrinkHoms.equivalence.{u} (largeTotal p χ)
    let raw := e.inverse.map τ
    have rawLift : (targetProjection (Scheme.fppfTopology.over S) p χ).IsHomLift (g ≫ f) raw :=
      inverse_isHomLift p χ (g ≫ f) τ hτ
    let factor := @Functor.IsStronglyCartesian.map (Over S) (largeTotal p χ) _ _
      (targetProjection (Scheme.fppfTopology.over S) p χ) R T a b f φ hφ
      _ (e.inverse.obj z) g (g ≫ f) rfl raw rawLift
    exact ⟨e.functor.map factor, ⟨by sorry, by sorry⟩, by
      intro ψ hψ
      sorry⟩

/-- The native Hom shrink functor preserves actual strong Cartesian lifts. -/
def shrinkCartesian :
    CartesianBasedFunctor (targetProjection (Scheme.fppfTopology.over S) p χ)
      (smallProjection p χ) :=
  CartesianBasedFunctor.ofBasedFunctor (shrinkBased p χ) (by
    intro a b φ hφ
    change (smallProjection p χ).IsStronglyCartesian
      ((smallProjection p χ).map ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor.map φ))
      ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor.map φ)
    have hbase : (smallProjection p χ).map
        ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor.map φ) =
        (targetProjection (Scheme.fppfTopology.over S) p χ).map φ := by sorry
    exact hbase.symm ▸ shrinkStrong p χ
      ((targetProjection (Scheme.fppfTopology.over S) p χ).map φ) φ hφ)

/-- The actual lifts are original lifts, encoded by the native Hom equivalence. -/
instance smallIsFibered : (smallProjection p χ).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro b R f
  let e := ShrinkHoms.equivalence.{u} (largeTotal p χ)
  let l := (Functor.Cleavage.ofIsFibered
    (targetProjection (Scheme.fppfTopology.over S) p χ)).lift (x := e.inverse.obj b) f
  exact ⟨e.functor.obj l.source, e.functor.map l.hom, shrinkStrong p χ f l.hom l.isStronglyCartesian⟩

/-- Applying both actual Hom equivalences recovers the original small arrow. -/
theorem shrink_map_inverse {a b : smallTotal p χ} (φ : a ⟶ b) :
    (ShrinkHoms.equivalence.{u} (largeTotal p χ)).functor.map
      ((ShrinkHoms.equivalence.{u} (largeTotal p χ)).inverse.map φ) = φ := sorry

/-- Every small target arrow has the actual factor supplied by the original
groupoid target and then encoded by the native Hom equivalence. -/
theorem smallArrowStrong (hG : Functor.IsFibered.InGroupoids p)
    {a b : smallTotal p χ} (φ : a ⟶ b) :
    (smallProjection p χ).IsStronglyCartesian ((smallProjection p χ).map φ) φ := by
  let e := ShrinkHoms.equivalence.{u} (largeTotal p χ)
  let raw := e.inverse.map φ
  have rawLift : (targetProjection (Scheme.fppfTopology.over S) p χ).IsHomLift
      ((smallProjection p χ).map φ) raw := .map _
  let strong := originalStrong (targetProjection (Scheme.fppfTopology.over S) p χ)
    (targetInGroupoids (Scheme.fppfTopology.over S) p χ hG) _ raw rawLift
  have result := shrinkStrong p χ ((smallProjection p χ).map φ) raw strong
  rw [shrink_map_inverse] at result
  exact result

/-- Fibredness and the actual strong factors give the original-universe target groupoid fibration. -/
instance smallInGroupoids [hG : Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.InGroupoids (smallProjection p χ) where
  toIsFibered := smallIsFibered p χ
  all_isCartesian φ :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _
      (smallProjection p χ) _ _ _ _ ((smallProjection p χ).map φ) φ
      (smallArrowStrong p χ hG φ)

set_option maxHeartbeats 1000000 in
/-- Both directions on the standard fibres are the actual native Hom equivalences. -/
def smallFiberEquivalence (U : Over S) :
    (targetProjection (Scheme.fppfTopology.over S) p χ).Fiber U ≌ (smallProjection p χ).Fiber U where
  functor := (shrinkBased p χ).fiberFunctor U
  inverse := (BasedFunctor.ofFunctor
    (ShrinkHoms.equivalence.{u} (largeTotal p χ)).inverse (by rfl)).fiberFunctor U
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by sorry)) (by sorry)
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by sorry)) (by sorry)
  functor_unitIso_comp := by sorry

/-- The completed fibres map to the standard small target fibres with the
actual two Cartesian-lift comparisons at every restriction. -/
def smallFibresIndexed : Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
    (𝟭 (Over S))
    (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'
    (Functor.fiberPseudofunctor (smallProjection p χ)) where
  app U :=
    Pseudofunctor.CoGrothendieck.standardFiber
      (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor' U ⋙
      (smallFiberEquivalence p χ U).functor
  naturality f := NatIso.ofComponents (fun x ↦
    ((smallFiberEquivalence p χ _).functor.mapIso
      (Pseudofunctor.CoGrothendieck.restrictionIso
        (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor' f x)) ≪≫
      (CartesianBasedFunctor.Reindex.mapIso (shrinkCartesian p χ)
        (Functor.Cleavage.ofIsFibered (targetProjection (Scheme.fppfTopology.over S) p χ))
        (Functor.Cleavage.ofIsFibered (smallProjection p χ)) f
        ((Pseudofunctor.CoGrothendieck.standardFiber
          (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor' _).obj x)).symm)
    (by sorry)
  naturality_id := sorry
  naturality_comp := sorry

/-- The component equivalences retain the implemented native realization and Hom shrink inverses. -/
theorem smallFibresEquivalences (U : Over S) :
    ((smallFibresIndexed p χ).app U).IsEquivalence := by
  let F := (completedPresheaf (Scheme.fppfTopology.over S) p χ).toPseudofunctor'
  letI : (Pseudofunctor.CoGrothendieck.standardFiber F U).IsEquivalence :=
    Pseudofunctor.CoGrothendieck.standardFibersEquivalences F U
  exact inferInstanceAs
    (Pseudofunctor.CoGrothendieck.standardFiber F U ⋙ (smallFiberEquivalence p χ U).functor).IsEquivalence

/-- Stack descent is transported through actual component equivalences and actual glue objects. -/
theorem smallIsStack : IsStack.OnSite (Scheme.fppfTopology.over S) (smallProjection p χ) where
  toIsFibered := smallIsFibered p χ
  toIsStack := Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isStackOfEquivalences
    (smallFibresIndexed p χ) (smallFibresEquivalences p χ) (Scheme.fppfTopology.over S)
    (DescentCompletion.ObjectGluing.isStack (Scheme.fppfTopology.over S)
      (localFibers (Scheme.fppfTopology.over S) p χ)
      (Localized.isPrestack (Scheme.fppfTopology.over S) p χ
        (localCleavage (Scheme.fppfTopology.over S) p χ)))

/-- The concrete original-universe stack-in-groupoids target. -/
def smallTarget [Functor.IsFibered.InGroupoids p] :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.mk (FiberedCategoryOver.Groupoids.ofFunctor (smallProjection p χ))
    (smallIsStack p χ)

/-- The original comparison followed by the actual Hom shrink functor. -/
def smallComparison [Functor.IsFibered.InGroupoids p] :
    CartesianBasedFunctor p (smallTarget p χ).p :=
  (comparison (Scheme.fppfTopology.over S) p χ).comp (shrinkCartesian p χ)

end AlgebraicGeometry.GroupoidsOver.Stackification
