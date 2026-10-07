module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Adjoining a Generic Point

This module owns the generic-point extension of a topological space.  Its
nonempty opens are obtained by adjoining the new point to an open of the
original space.  The resulting functor on opens is a cover-dense basis, and
the `Opens` namespace records the induced site and its comparison equivalence.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u v w

namespace TopCat.GenericPoint

/-- The predicate defining the opens of the generic-point extension of `X`. -/
def isOpen (X : TopCat.{u}) (s : Set (Option X)) : Prop :=
  s = ∅ ∨ none ∈ s ∧ IsOpen ((Option.some : X → Option X) ⁻¹' s)

/-- The whole generic-point extension is open. -/
theorem isOpen_univ (X : TopCat.{u}) :
    isOpen X (Set.univ : Set (Option X)) := sorry

/-- The generic-point open predicate is closed under binary intersections. -/
theorem isOpen_inter (X : TopCat.{u}) {s t : Set (Option X)}
    (hs : isOpen X s) (ht : isOpen X t) :
    isOpen X (s ∩ t) := sorry

/-- Taking preimages along `Option.some` commutes with unions of sets. -/
theorem preimage_some_sUnion (X : TopCat.{u}) (S : Set (Set (Option X))) :
    ((Option.some : X → Option X) ⁻¹' ⋃₀ S) =
      ⋃₀ (((Option.some : X → Option X) ⁻¹' ·) '' S) := sorry

/-- The generic-point open predicate is closed under arbitrary unions. -/
theorem isOpen_sUnion (X : TopCat.{u}) {S : Set (Set (Option X))}
    (hS : ∀ s ∈ S, isOpen X s) :
    isOpen X (⋃₀ S) := sorry

/-- The topology on `Option X` whose nonempty opens are `U ∪ {none}` for open `U` in `X`. -/
@[reducible]
def topology (X : TopCat.{u}) : TopologicalSpace (Option X) where
  IsOpen := isOpen X
  isOpen_univ := isOpen_univ X
  isOpen_inter _ _ := isOpen_inter X
  isOpen_sUnion _ := isOpen_sUnion X

/-- The topological space obtained by adjoining one generic point to `X`. -/
def extension (X : TopCat.{u}) : TopCat.{u} where
  carrier := Option X
  str := topology X

/-- A subset containing the generic point is determined by its ordinary points. -/
theorem eq_insert_image (X : TopCat.{u}) {s : Set (Option X)} (hs : none ∈ s) :
    s = Set.insert (none : Option X)
      (Option.some '' ((Option.some : X → Option X) ⁻¹' s)) := sorry

/-- Pulling `insert none (Option.some '' U)` back along `Option.some` recovers `U`. -/
theorem preimage_insert (U : Set X) :
    ((Option.some : X → Option X) ⁻¹' Set.insert (none : Option X) (Option.some '' U)) = U := sorry

/-- The canonical inclusion of `X` into its generic-point extension. -/
def inclusion (X : TopCat.{u}) : X ⟶ extension X :=
  -- `Option X` has no ambient topology until it is viewed as the carrier of `extension X`.
  letI : TopologicalSpace (Option X) := topology X
  TopCat.ofHom ⟨fun x ↦ (Option.some x : extension X), sorry⟩

/-- The inclusion sends an ordinary point to its `Option.some` image. -/
@[simp]
theorem inclusion_apply (X : TopCat.{u}) (x : X) :
    inclusion X x = (Option.some x : extension X) := sorry

/-- The canonical inclusion induces the original topology on `X`. -/
theorem inclusion_isInducing (X : TopCat.{u}) :
    Topology.IsInducing (inclusion X) := sorry

/-- The opens of the generic-point extension are exactly the empty set and the basic opens. -/
theorem isOpen_iff (X : TopCat.{u}) {s : Set (extension X)} :
    IsOpen s ↔
      s = ∅ ∨ ∃ U : Set X, IsOpen U ∧
        s = Set.insert (none : extension X)
          ((Option.some : X → extension X) '' U) := sorry

/-- A basic generic-point open is open whenever its ordinary part is open. -/
theorem isOpen_basic (X : TopCat.{u}) {U : Set X} (hU : IsOpen U) :
    IsOpen
      ((Set.insert (none : extension X)
          ((Option.some : X → extension X) '' U)) : Set (extension X)) := sorry

/-- The basic open of the generic-point extension corresponding to `U`. -/
def basicOpen (X : TopCat.{u}) (U : Opens X) : Opens (extension X) :=
  ⟨((Set.insert (none : extension X)
      ((Option.some : X → extension X) '' (U : Set X))) : Set (extension X)),
    isOpen_basic X U.2⟩

/-- Membership in a basic generic-point open is its explicit set-theoretic condition. -/
@[simp]
theorem mem_basicOpen_iff (X : TopCat.{u}) (U : Opens X) {x : extension X} :
    x ∈ basicOpen X U ↔
      x ∈ Set.insert (none : extension X)
        ((Option.some : X → extension X) '' (U : Set X)) := sorry

/-- Pulling a basic generic-point open back along the inclusion recovers its ordinary part. -/
theorem map_basicOpen (X : TopCat.{u}) (U : Opens X) :
    (Opens.map (inclusion X)).obj (basicOpen X U) = U := sorry

/-- The functor on opens induced by the canonical inclusion. -/
noncomputable def basis (X : TopCat.{u}) : Opens X ⥤ Opens (extension X) :=
  (inclusion_isInducing X).functor

/-- The canonical basis functor sends `U` to the corresponding basic open. -/
@[simp]
theorem basis_obj_eq_basicOpen (X : TopCat.{u}) (U : Opens X) :
    (basis X).obj U = basicOpen X U := sorry

/-- Membership in the basis image has the explicit `U ∪ {none}` description. -/
@[simp]
theorem mem_basis_obj_iff (X : TopCat.{u}) (U : Opens X) {x : extension X} :
    x ∈ (basis X).obj U ↔
      x ∈ Set.insert (none : extension X)
        ((Option.some : X → extension X) '' (U : Set X)) := sorry

/-- The generic-point basis functor is full. -/
instance basis_full (X : TopCat.{u}) : Functor.Full (basis X) := sorry

/-- The generic-point basis functor is faithful. -/
instance basis_faithful (X : TopCat.{u}) : Functor.Faithful (basis X) := sorry

/-- The image of the generic-point basis functor is a basis of opens. -/
theorem basis_isBasis (X : TopCat.{u}) :
    Opens.IsBasis (Set.range (basis X).obj) := sorry

/-- The generic-point basis functor is cover-dense for the opens topology upstairs. -/
instance basis_isCoverDense (X : TopCat.{u}) :
    (basis X).IsCoverDense (Opens.grothendieckTopology (extension X)) := sorry

namespace Opens

/-- The textbook covering predicate on the opens of `X` induced by adjoining a generic point. -/
def covering (X : TopCat.{u}) {U : Opens X} (R : Presieve U) : Prop :=
  (∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U), R f ∧ x ∈ V) ∧
    (U = ⊥ → ∃ (V : Opens X) (f : V ⟶ U), R f)

/-- The Grothendieck topology on `Opens X` induced by the generic-point basis. -/
noncomputable def topology (X : TopCat.{u}) : GrothendieckTopology (Opens X) :=
  (basis X).inducedTopology (Opens.grothendieckTopology (extension X))

/-- A generic-point covering family contains an arrow. -/
theorem covering_exists_arrow (X : TopCat.{u}) {U : Opens X} {R : Presieve U}
    (hR : covering X R) :
    ∃ (V : Opens X) (f : V ⟶ U), R f := sorry

/-- The explicit generic-point covering predicate presents the induced opens topology. -/
theorem covering_iff_mem_topology (X : TopCat.{u}) {U : Opens X} {R : Presieve U} :
    covering X R ↔ Sieve.generate R ∈ topology X U := sorry

/-- The identity family on the empty open is a generic-point covering. -/
theorem covering_bot_singleton (X : TopCat.{u}) :
    covering X (Presieve.singleton (𝟙 (⊥ : Opens X))) := sorry

/-- The comparison equivalence from generic-point opens to sheaves on the extension. -/
noncomputable def sheafEquiv (X : TopCat.{u}) (C : Type v) [Category.{w} C]
    [∀ U : (Opens (extension X))ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow U (basis X).op) C] :
    _root_.CategoryTheory.Sheaf (topology X) C ≌
      _root_.CategoryTheory.Sheaf (Opens.grothendieckTopology (extension X)) C :=
  (basis X).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology (extension X)) C

/-- Type has the structured-arrow limits needed for generic-point sheaf comparison. -/
instance type_hasLimits (X : TopCat.{u}) :
    ∀ U : (Opens (extension X))ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow U (basis X).op) (Type (max u v)) :=
  fun _ ↦ inferInstance

/-- The Type-valued generic-point comparison without extra ambient limit arguments. -/
noncomputable def typeSheafEquiv (X : TopCat.{u}) :
    _root_.CategoryTheory.Sheaf (topology X) (Type (max u v)) ≌
      TopCat.Sheaf (Type (max u v)) (extension X) :=
  sheafEquiv X (Type (max u v))

end Opens

end TopCat.GenericPoint
