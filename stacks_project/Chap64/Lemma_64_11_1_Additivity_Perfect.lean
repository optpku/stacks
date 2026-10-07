module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Derived.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.Quotient
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import stacks_project.Chap64.Lemma_64_11_2_Filtered

/-!
# Filtered perfect complexes

Bounded cochain complexes of filtered finite projective objects of `Filᶠ(ModuleCat Λ)`,
the homotopy category `KF_perf(Λ)`, and the essential image `DF_perf(Λ)` in the finite
filtered derived category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open scoped FilteredObject.Finite ZeroObject

universe u

namespace CochainComplex

variable {Λ : Type u} [Ring Λ]

/-- A cochain complex of finite filtered left `Λ`-modules is bounded filtered finite
projective when it is bounded on both sides and each term is a filtered finite
projective object of `Filᶠ(ModuleCat Λ)`. -/
class IsBoundedFilteredFiniteProjective
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) : Prop where
  /-- The complex is bounded on both sides. -/
  bounded : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b
  /-- Each term is a filtered finite projective object. -/
  filteredFiniteProjective (n : ℤ) :
    FilteredObject.IsFilteredFiniteProjective (P.X n).obj

/-- A cochain complex is bounded filtered finite projective exactly when it is bounded
and every term is filtered finite projective. -/
theorem isBoundedFilteredFiniteProjective_iff
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :
    IsBoundedFilteredFiniteProjective P ↔
      (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
        ∀ n : ℤ, FilteredObject.IsFilteredFiniteProjective (P.X n).obj :=
  sorry

/-- The zero complex of finite filtered modules is bounded filtered finite projective. -/
noncomputable instance instIsBoundedFilteredFiniteProjectiveZero :
    IsBoundedFilteredFiniteProjective (0 : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :=
  sorry

/-- Forgetting the finite filtration of a bounded filtered finite-projective complex
yields a bounded finite-projective cochain complex. -/
instance instIsBoundedFiniteProjective_forget
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [IsBoundedFilteredFiniteProjective P] :
    ((FilteredObject.Finite.Forget.cochain (ModuleCat.{u} Λ)).obj P).IsBoundedFiniteProjective :=
  sorry

end CochainComplex

namespace CategoryTheory.FilteredObject.Finite.GradedPiece

variable {Λ : Type u} [Ring Λ]

/-- Termwise `p`-th associated graded of a cochain complex of finite filtered modules. -/
noncomputable abbrev cochain (p : ℤ) :
    CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ ⥤ CochainComplex (ModuleCat.{u} Λ) ℤ :=
  AssociatedGraded.cochain (ModuleCat.{u} Λ) ⋙
    (GradedObject.eval p).mapHomologicalComplex (up ℤ)

end CategoryTheory.FilteredObject.Finite.GradedPiece

namespace CochainComplex

variable {Λ : Type u} [Ring Λ]

/-- Each associated-graded piece of a bounded filtered finite-projective complex is a
bounded finite-projective cochain complex. -/
instance instIsBoundedFiniteProjective_gradedPiece
    (P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [IsBoundedFilteredFiniteProjective P] (p : ℤ) :
    ((FilteredObject.Finite.GradedPiece.cochain p).obj P).IsBoundedFiniteProjective :=
  sorry

end CochainComplex

namespace CategoryTheory.HomotopyCategory

variable (Λ : Type u) [Ring Λ]

/-- Homotopy-category objects whose underlying cochain complex is bounded and termwise
filtered finite projective. -/
protected def filteredPerfect :
    ObjectProperty (HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)) :=
  fun K ↦ CochainComplex.IsBoundedFilteredFiniteProjective K.as

/-- Membership in the filtered-perfect homotopy-category owner is bounded filtered finite
projectivity of the underlying complex. -/
lemma filteredPerfect_iff (K : HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)) :
    HomotopyCategory.filteredPerfect Λ K ↔
      CochainComplex.IsBoundedFilteredFiniteProjective K.as :=
  sorry

/-- The homotopy category of bounded complexes of filtered finite projective objects of
`Filᶠ(ModuleCat Λ)`. -/
abbrev FilteredPerfect := (HomotopyCategory.filteredPerfect Λ).FullSubcategory

namespace FilteredPerfect

/-- The inclusion of the filtered-perfect homotopy category into the ambient homotopy
category of finite filtered complexes. -/
abbrev ι : FilteredPerfect Λ ⥤ HomotopyCategory (Filᶠ(ModuleCat.{u} Λ)) (up ℤ) :=
  (HomotopyCategory.filteredPerfect Λ).ι

/-- The homotopy class of a bounded filtered finite-projective cochain complex, as an
object of the filtered-perfect homotopy category. -/
def ofComplex (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [hL : CochainComplex.IsBoundedFilteredFiniteProjective L] : FilteredPerfect Λ :=
  ⟨(HomotopyCategory.quotient (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)).obj L, hL⟩

/-- The underlying cochain complex of `ofComplex L` is `L`. -/
theorem ofComplex_as (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    [CochainComplex.IsBoundedFilteredFiniteProjective L] :
    (ofComplex Λ L).obj.as = L :=
  sorry

variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The canonical functor from the filtered-perfect homotopy category to the finite
filtered derived category. -/
def toDerived :
    FilteredPerfect Λ ⥤
      FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ) :=
  ι Λ ⋙ FilteredObject.FiniteDerived.Quotient.functor (ModuleCat.{u} Λ)

/-- The functor from the filtered-perfect homotopy category to the finite filtered
derived category is full. -/
instance instFullToDerived : (toDerived Λ).Full := sorry

/-- The functor from the filtered-perfect homotopy category to the finite filtered
derived category is faithful. -/
instance instFaithfulToDerived : (toDerived Λ).Faithful := sorry

/-- Hom-sets in the filtered-perfect homotopy category map bijectively to Hom-sets in
the finite filtered derived category. -/
theorem toDerived_map_bijective {P Q : FilteredPerfect Λ} :
    Function.Bijective
      ((toDerived Λ).map : (P ⟶ Q) → ((toDerived Λ).obj P ⟶ (toDerived Λ).obj Q)) :=
  sorry

end FilteredPerfect

end CategoryTheory.HomotopyCategory

namespace CategoryTheory.FilteredObject.FiniteDerived.Quotient

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The image of a cochain complex of finite filtered modules in `DF(ModuleCat Λ)`. -/
noncomputable abbrev ofCochainComplex
    (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ) :
    Category (ModuleCat.{u} Λ) :=
  (functor (ModuleCat.{u} Λ)).obj
    ((HomotopyCategory.quotient (Filᶠ(ModuleCat.{u} Λ)) (up ℤ)).obj L)

end CategoryTheory.FilteredObject.FiniteDerived.Quotient

namespace CategoryTheory.FilteredObject.FiniteDerived

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- An object of `DF(ModuleCat Λ)` is perfect if it is isomorphic to the image of a
bounded cochain complex of filtered finite projective objects of `Filᶠ(ModuleCat Λ)`. -/
def IsPerfect (K : Quotient.Category (ModuleCat.{u} Λ)) : Prop :=
  ∃ (L : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ)
    (_ : K ≅ Quotient.ofCochainComplex L),
    CochainComplex.IsBoundedFilteredFiniteProjective L

namespace IsPerfect

/-- Perfectness in the finite filtered derived category is invariant under
isomorphism. -/
theorem of_iso {K L : Quotient.Category (ModuleCat.{u} Λ)} (e : K ≅ L)
    (hL : IsPerfect L) : IsPerfect K :=
  sorry

variable [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- Forgetting the filtration of a filtered-perfect derived object yields a perfect
object of `D(ModuleCat Λ)`. -/
theorem forget {K : Quotient.Category (ModuleCat.{u} Λ)} (hK : IsPerfect K) :
    DerivedCategory.IsPerfect ((Forget.canonicalLift (ModuleCat.{u} Λ)).obj K) :=
  sorry

/-- Each associated-graded piece of a filtered-perfect derived object is a perfect
object of `D(ModuleCat Λ)`. -/
theorem gradedPiece {K : Quotient.Category (ModuleCat.{u} Λ)} (hK : IsPerfect K)
    (p : ℤ) :
    DerivedCategory.IsPerfect ((GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).obj K) :=
  sorry

end IsPerfect

end CategoryTheory.FilteredObject.FiniteDerived

namespace CategoryTheory.HomotopyCategory.FilteredPerfect

variable {Λ : Type u} [Ring Λ]
variable [CategoryWithHomology (GradedObject ℤ (ModuleCat.{u} Λ))]

/-- The essential image of the filtered-perfect homotopy category in `DF(ModuleCat Λ)`
is the class of filtered-perfect derived objects. -/
theorem mem_essImage_toDerived_iff
    (K : FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ)) :
    (toDerived Λ).essImage K ↔ FilteredObject.FiniteDerived.IsPerfect K :=
  sorry

end CategoryTheory.HomotopyCategory.FilteredPerfect
