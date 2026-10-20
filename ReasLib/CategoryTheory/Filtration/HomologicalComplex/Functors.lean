module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.CategoryTheory.Filtration.Functors

/-!
# Functors on Filtered Homological Complexes

This module owns the shape-independent functors on a homological complex in filtered objects:
forgetting the filtration, evaluating a filtration stage, and passing to associated graded pieces.
The homology-specific API is kept in `HomologicalComplex/Homology`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- The functor forgetting the filtration on a homological complex in filtered objects. -/
@[stacks 012C "underlying functor of a filtered homological complex"]
abbrev underlyingFunctor :
    HomologicalComplex (FilteredObject C) c ⥤ HomologicalComplex C c :=
  FilteredObject.forget.mapHomologicalComplex c

/-- Forget the filtration on a homological complex in filtered objects. -/
abbrev underlying (K : HomologicalComplex (FilteredObject C) c) : HomologicalComplex C c :=
  underlyingFunctor.obj K

/-- The morphism on underlying homological complexes induced by a filtered-complex morphism. -/
@[stacks 012C "underlying map of a filtered homological complex"]
abbrev underlyingMap {K L : HomologicalComplex (FilteredObject C) c} (f : K ⟶ L) :
    underlying K ⟶ underlying L :=
  underlyingFunctor.map f

/-- The underlying map induced by an identity filtered-complex morphism is the identity. -/
@[simp, stacks 012C "identity underlying map of a filtered homological complex"]
theorem underlyingMap_id (K : HomologicalComplex (FilteredObject C) c) :
    underlyingMap (𝟙 K) = 𝟙 (underlying K) := sorry

/-- Underlying maps of filtered homological complexes preserve composition. -/
@[simp, stacks 012C "composition of underlying maps of filtered homological complexes"]
theorem underlyingMap_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) :
    underlyingMap (f ≫ g) = underlyingMap f ≫ underlyingMap g := sorry

namespace Stage

/-- Evaluation at filtration stage `p`, applied degreewise to filtered homological complexes. -/
@[stacks 012C "filtration-stage functor on filtered homological complexes"]
abbrev functor (p : ℤ) :
    HomologicalComplex (FilteredObject C) c ⥤ HomologicalComplex C c :=
  (FilteredObject.Stage.functor p).mapHomologicalComplex c

/-- Evaluate a homological complex in filtered objects at filtration stage `p`. -/
@[stacks 012C "filtered stage complex"]
abbrev complex (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    HomologicalComplex C c :=
  (functor p).obj K

/-- The morphism on `p`-th stage complexes induced by a filtered-complex morphism. -/
@[stacks 012C "map of filtered stage complexes"]
abbrev map {K L : HomologicalComplex (FilteredObject C) c} (f : K ⟶ L) (p : ℤ) :
    complex K p ⟶ complex L p :=
  (functor p).map f

/-- The map on a filtration-stage complex induced by an identity is the identity. -/
@[simp, stacks 012C "identity map of a filtered stage complex"]
theorem map_id (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    map (𝟙 K) p = 𝟙 (complex K p) := sorry

/-- Maps on a fixed filtration stage preserve composition. -/
@[simp, stacks 012C "composition of maps of filtered stage complexes"]
theorem map_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

/-- The canonical map from filtration stage `q` to filtration stage `p` when `p ≤ q`. -/
@[stacks 012C "stage comparison"]
abbrev comparison (K : HomologicalComplex (FilteredObject C) c) {p q : ℤ}
    (hpq : p ≤ q) : complex K q ⟶ complex K p :=
  (NatTrans.mapHomologicalComplex (FilteredObject.Stage.mapOfLE hpq) c).app K

/-- The comparison from a filtration stage to itself is the identity. -/
@[simp, stacks 012C "identity filtered stage comparison"]
theorem comparison_refl (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    comparison K (le_refl p) = 𝟙 (complex K p) := sorry

/-- Successive stage comparisons compose to the direct stage comparison. -/
@[simp, stacks 012C "composition of filtered stage comparisons"]
theorem comparison_comp (K : HomologicalComplex (FilteredObject C) c) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    comparison K hqr ≫ comparison K hpq = comparison K (hpq.trans hqr) := sorry

/-- The canonical inclusion of a filtration-stage complex into the underlying complex. -/
@[stacks 012C "stage inclusion"]
abbrev inclusion (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    complex K p ⟶ underlying K :=
  (NatTrans.mapHomologicalComplex (FilteredObject.Stage.toForget p) c).app K

namespace Inclusion

/-- A filtered-complex morphism commutes with the inclusion of each filtration stage into the
underlying complex. -/
@[reassoc, stacks 012C "naturality of filtered stage inclusion"]
theorem naturality {K L : HomologicalComplex (FilteredObject C) c} (f : K ⟶ L) (p : ℤ) :
    map f p ≫ inclusion L p = inclusion K p ≫ underlyingMap f := sorry

end Inclusion

/-- A later filtration stage includes into the underlying complex through every earlier stage. -/
@[stacks 012C "factorization of a filtered stage inclusion"]
theorem comparison_comp_inclusion
    (K : HomologicalComplex (FilteredObject C) c) {p q : ℤ} (hpq : p ≤ q) :
    comparison K hpq ≫ inclusion K p = inclusion K q := sorry

namespace Comparison

/-- A filtered-complex morphism commutes with every filtration-stage comparison. -/
@[reassoc, stacks 012C "naturality of filtered stage comparison"]
theorem naturality {K L : HomologicalComplex (FilteredObject C) c} (f : K ⟶ L) {p q : ℤ}
    (hpq : p ≤ q) :
    comparison K hpq ≫ map f p = map f q ≫ comparison L hpq := sorry

end Comparison

end Stage

section Graded

variable [HasCokernels C]

/-- Apply the associated-graded functor degreewise to filtered homological complexes. -/
@[stacks 012C "associated-graded functor on filtered homological complexes"]
noncomputable abbrev associatedGradedFunctor :
    HomologicalComplex (FilteredObject C) c ⥤
      HomologicalComplex (GradedObject ℤ C) c :=
  FilteredObject.associatedGradedFunctor.mapHomologicalComplex c

/-- Apply the associated-graded functor degreewise to a filtered homological complex. -/
noncomputable abbrev associatedGraded
    (K : HomologicalComplex (FilteredObject C) c) :
    HomologicalComplex (GradedObject ℤ C) c :=
  associatedGradedFunctor.obj K

/-- The map on associated-graded homological complexes induced by a filtered-complex morphism. -/
@[stacks 012C "map of associated-graded homological complexes"]
noncomputable abbrev associatedGradedMap {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) : associatedGraded K ⟶ associatedGraded L :=
  associatedGradedFunctor.map f

/-- The associated-graded map induced by an identity is the identity. -/
@[simp, stacks 012C "identity map of associated-graded homological complexes"]
theorem associatedGradedMap_id (K : HomologicalComplex (FilteredObject C) c) :
    associatedGradedMap (𝟙 K) = 𝟙 (associatedGraded K) := sorry

/-- Associated-graded maps of filtered homological complexes preserve composition. -/
@[simp, stacks 012C "composition of maps of associated-graded homological complexes"]
theorem associatedGradedMap_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) :
    associatedGradedMap (f ≫ g) = associatedGradedMap f ≫ associatedGradedMap g := sorry

/-- Evaluation of the associated graded object in degree `p`, applied degreewise to filtered
homological complexes. -/
@[stacks 012C "graded-piece functor on filtered homological complexes"]
noncomputable abbrev gradedPieceFunctor (p : ℤ) :
    HomologicalComplex (FilteredObject C) c ⥤ HomologicalComplex C c :=
  (FilteredObject.associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex c

/-- The `p`-th graded-piece homological complex of a filtered homological complex. -/
@[stacks 012C "graded piece of a filtered homological complex"]
noncomputable abbrev gradedPiece
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    HomologicalComplex C c :=
  (gradedPieceFunctor p).obj K

/-- The map on `p`-th graded-piece complexes induced by a filtered-complex morphism. -/
@[stacks 012C "map of graded-piece homological complexes"]
noncomputable abbrev gradedPieceMap {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) : gradedPiece K p ⟶ gradedPiece L p :=
  (gradedPieceFunctor p).map f

/-- The graded-piece map induced by an identity is the identity. -/
@[simp, stacks 012C "identity map of a graded-piece homological complex"]
theorem gradedPieceMap_id (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) :
    gradedPieceMap (𝟙 K) p = 𝟙 (gradedPiece K p) := sorry

/-- Maps on a fixed graded-piece complex preserve composition. -/
@[simp, stacks 012C "composition of maps of graded-piece homological complexes"]
theorem gradedPieceMap_comp {K L M : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := sorry

end Graded

end HomologicalComplex.Filtered
end CategoryTheory
