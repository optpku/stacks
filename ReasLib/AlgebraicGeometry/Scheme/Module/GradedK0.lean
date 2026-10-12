/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Additivity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension.Serre
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.SerreQuotient

/-!
# Cycles and the dimension-graded Grothendieck group

This file defines the Serre quotient of coherent sheaves in two consecutive support
dimensions and the two concrete additive maps comparing its Grothendieck group with cycles.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Inside coherent sheaves supported in dimension at most `k`, the objects supported in
dimension at most `k - 1`. -/
def lowerCoh {X : Scheme.{u}} (d : X → ℤ) (k : ℤ) :
    ObjectProperty (RingedSpace.CohLE X.toRingedSpace d k) :=
  (RingedSpace.Coh.supportDimensionLE d (k - 1)).inverseImage
    (RingedSpace.Coh.supportDimensionLE d k).ι

/-- Membership in `lowerCoh d k` is the pointwise support bound `d x ≤ k - 1`. -/
theorem lowerCoh_iff {X : Scheme.{u}} (d : X → ℤ) (k : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace d k) :
    lowerCoh d k F ↔
      ∀ x ∈ RingedSpace.moduleSupport F.obj.obj, d x ≤ k - 1 := sorry

/-- The lower-dimensional coherent objects form the canonical Serre class in the
upper-dimensional coherent category. -/
instance lowerCohIsSerreClass
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (lowerCoh (f.relativeDimensionFunction δ) k).IsSerreClass := sorry

/-- The Serre quotient `Coh≤k(X) / Coh≤k-1(X)` for the relative dimension function. -/
abbrev GradedCoh
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (lowerCoh (f.relativeDimensionFunction δ) k).isoModSerre.Localization

/-- The quotient image of an object of `Coh≤k(X)`. -/
noncomputable def gradedQuotientObj
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    GradedCoh f δ k :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (lowerCoh (f.relativeDimensionFunction δ) k).isoModSerre.Q.obj F

/-- The quotient-object construction is the object map of the canonical Serre quotient. -/
theorem gradedQuotientObj_eq
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
    -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    gradedQuotientObj f δ k F =
      (lowerCoh (f.relativeDimensionFunction δ) k).isoModSerre.Q.obj F := sorry

/-- The Grothendieck group of `Coh≤k(X) / Coh≤k-1(X)`. -/
abbrev GradedK0
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :=
  AbelianK0 (GradedCoh f δ k)

namespace GradedK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- The Grothendieck class of a coherent object after passage to the graded Serre quotient. -/
noncomputable def of
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    GradedK0 f δ k :=
  AbelianK0.of (gradedQuotientObj f δ k F)

/-- `of` is the class of the canonical quotient object. -/
theorem of_def
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    of f δ k F = AbelianK0.of (gradedQuotientObj f δ k F) := sorry

/-- The coproduct of reduced point-closure structure sheaves indexed by the positive
coefficients of a cycle. -/
noncomputable def positiveModule
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) : X.Modules :=
  ∐ fun i : Σ x : X, Fin (Int.toNat (α.1 x)) ↦
    closedSubschemeStructureSheafOn (PointClosure.reducedStructure i.1).ideal

/-- The positive coproduct attached to a cycle is coherent. -/
instance positiveModuleIsCoherent
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    (positiveModule f δ k α).IsCoherent := sorry

/-- The positive coproduct attached to a degree-`k` cycle is supported in dimension at most
`k`. -/
theorem positiveModule_support_le
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    ∀ x ∈ RingedSpace.moduleSupport (positiveModule f δ k α),
      f.relativeDimensionFunction δ x ≤ k := sorry

/-- The positive coproduct, bundled as an object of `Coh≤k(X)`. -/
noncomputable def positiveObject
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k :=
  ⟨⟨positiveModule f δ k α, positiveModuleIsCoherent f δ k α⟩,
    (RingedSpace.Coh.supportDimensionLE_iff
      (f.relativeDimensionFunction δ) k _).2 (positiveModule_support_le f δ k α)⟩

/-- The underlying module of `positiveObject` is its explicit locally finite coproduct. -/
theorem positiveObject_obj
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    (positiveObject f δ k α).obj.obj = positiveModule f δ k α := sorry

/-- The coproduct of reduced point-closure structure sheaves indexed by the absolute values
of the negative coefficients of a cycle. -/
noncomputable def negativeModule
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) : X.Modules :=
  ∐ fun i : Σ x : X, Fin (Int.toNat (-α.1 x)) ↦
    closedSubschemeStructureSheafOn (PointClosure.reducedStructure i.1).ideal

/-- The negative coproduct attached to a cycle is coherent. -/
instance negativeModuleIsCoherent
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    (negativeModule f δ k α).IsCoherent := sorry

/-- The negative coproduct attached to a degree-`k` cycle is supported in dimension at most
`k`. -/
theorem negativeModule_support_le
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    ∀ x ∈ RingedSpace.moduleSupport (negativeModule f δ k α),
      f.relativeDimensionFunction δ x ≤ k := sorry

/-- The negative coproduct, bundled as an object of `Coh≤k(X)`. -/
noncomputable def negativeObject
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k :=
  ⟨⟨negativeModule f δ k α, negativeModuleIsCoherent f δ k α⟩,
    (RingedSpace.Coh.supportDimensionLE_iff
      (f.relativeDimensionFunction δ) k _).2 (negativeModule_support_le f δ k α)⟩

/-- The underlying module of `negativeObject` is its explicit locally finite coproduct. -/
theorem negativeObject_obj
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    (negativeObject f δ k α).obj.obj = negativeModule f δ k α := sorry

/-- The value of the cycle-to-`K₀` map: the positive coproduct class minus the negative
coproduct class. -/
noncomputable def toK0Value
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) : GradedK0 f δ k :=
  of f δ k (positiveObject f δ k α) - of f δ k (negativeObject f δ k α)

/-- The cycle-to-`K₀` value sends zero to zero. -/
theorem toK0Value_zero : toK0Value f δ k 0 = 0 := sorry

/-- The cycle-to-`K₀` value preserves addition. -/
theorem toK0Value_add
    (α β : CycleGroup X (f.relativeDimensionFunction δ) k) :
    toK0Value f δ k (α + β) = toK0Value f δ k α + toK0Value f δ k β := sorry

/-- The additive map from degree-`k` cycles to the Grothendieck group of the graded coherent
quotient. -/
noncomputable def toK0 :
    CycleGroup X (f.relativeDimensionFunction δ) k →+ GradedK0 f δ k where
  toFun := toK0Value f δ k
  map_zero' := toK0Value_zero f δ k
  map_add' := toK0Value_add f δ k

/-- The map `toK0` is computed by the difference of the explicit positive and negative
coproduct classes. -/
theorem toK0_apply (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    toK0 f δ k α =
      of f δ k (positiveObject f δ k α) - of f δ k (negativeObject f δ k α) := sorry

/-- On a point cycle, `toK0` is the quotient class of the reduced point-closure structure
sheaf. -/
theorem toK0_point (x : X) (hx : f.relativeDimensionFunction δ x = k) :
    toK0 f δ k (CycleGroup.point (f.relativeDimensionFunction δ) k x hx) =
      of f δ k
        ⟨⟨closedSubschemeStructureSheafOn (PointClosure.reducedStructure x).ideal,
            @PointClosure.instIsCoherentStructureSheafOn X
              (LocallyOfFiniteType.isLocallyNoetherian f) x⟩,
          (RingedSpace.Coh.supportDimensionLE_iff
            (f.relativeDimensionFunction δ) k _).2
            (PointClosure.structureSheafOn_support_le f δ k x hx)⟩ := sorry

/-- The cycle associated to an object of `Coh≤k(X)`. -/
noncomputable def objectCycle
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    CycleGroup X (f.relativeDimensionFunction δ) k :=
  ⟨@associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) F.obj.obj
      F.obj.property (f.relativeDimensionFunction δ) k,
    @associatedCycle_mem_dimensionSubgroup X
      (LocallyOfFiniteType.isLocallyNoetherian f) F.obj.obj F.obj.property
      (f.relativeDimensionFunction δ) k⟩

/-- The underlying algebraic cycle of `objectCycle F` is the existing associated cycle of
the coherent module `F`. -/
theorem objectCycle_apply
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) (x : X) :
    CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k
        (objectCycle f δ k F) x =
      @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) F.obj.obj
        F.obj.property (f.relativeDimensionFunction δ) k x := sorry

/-- The associated-cycle object function kills the defining short-exact relations in
`Coh≤k(X)`. -/
theorem objectCycle_relations_le_ker :
    AbelianK0.relations
        (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) ≤
      (FreeAbelianGroup.lift (objectCycle f δ k)).ker := sorry

/-- The associated-cycle homomorphism on `K₀(Coh≤k(X))`. -/
noncomputable def upperToCycle :
    AbelianK0 (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) →+
      CycleGroup X (f.relativeDimensionFunction δ) k :=
  AbelianK0.lift (objectCycle f δ k) (objectCycle_relations_le_ker f δ k)

/-- The upper associated-cycle homomorphism sends an object class to its associated cycle. -/
theorem upperToCycle_of
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    upperToCycle f δ k (AbelianK0.of F) = objectCycle f δ k F := sorry

/-- The canonical surjection from `K₀(Coh≤k(X))` to the graded Grothendieck group. -/
noncomputable abbrev quotientK0 :
    AbelianK0 (RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) →+
      GradedK0 f δ k :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ObjectProperty.SerreClassLocalization.quotientK0
    (lowerCoh (f.relativeDimensionFunction δ) k)

/-- The kernel of the quotient map is contained in the kernel of the associated-cycle map. -/
theorem quotientKer_le_upperToCycleKer :
    (quotientK0 f δ k).ker ≤ (upperToCycle f δ k).ker := sorry

/-- The associated-cycle homomorphism descended to the graded Serre quotient. -/
noncomputable def toCycle :
    GradedK0 f δ k →+ CycleGroup X (f.relativeDimensionFunction δ) k :=
  -- The morphism `f` canonically supplies `IsLocallyNoetherian X`.
  -- Local instance justification (proof-local temporary data): `f` is not inferable from `X`.
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (quotientK0 f δ k).liftOfSurjective
    (ObjectProperty.SerreClassLocalization.quotientK0_surjective
      (lowerCoh (f.relativeDimensionFunction δ) k))
    ⟨upperToCycle f δ k, quotientKer_le_upperToCycleKer f δ k⟩

/-- Descending `upperToCycle` through the quotient commutes with the quotient map. -/
theorem toCycle_comp_quotientK0 :
    (toCycle f δ k).comp (quotientK0 f δ k) = upperToCycle f δ k := sorry

/-- The descended map sends the quotient class of a coherent object to its associated cycle. -/
theorem toCycle_of
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    toCycle f δ k (of f δ k F) = objectCycle f δ k F := sorry

/-- The descended associated-cycle map is uniquely characterized by its composite with the
surjective quotient map. -/
theorem toCycle_unique
    (g : GradedK0 f δ k →+ CycleGroup X (f.relativeDimensionFunction δ) k)
    (hg : g.comp (quotientK0 f δ k) = upperToCycle f δ k) :
    g = toCycle f δ k := sorry

end GradedK0

end AlgebraicGeometry.Scheme.Modules
