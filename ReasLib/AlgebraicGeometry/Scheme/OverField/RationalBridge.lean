/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.SeparableDegree
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RationalBridge

/-- The reduced component subscheme associated to an irreducible component. -/
noncomputable abbrev componentScheme
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

/-- The structure morphism of the reduced component is induced from the ambient scheme. -/
theorem componentScheme_spec
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (componentScheme X Z).hom = X.left.irreducibleComponentSubschemeι Z ≫ X.hom := sorry

/-- The open complement of the chosen reduced component. -/
noncomputable def complement
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : X.left.Opens :=
  closedImmersionComplement (X.left.irreducibleComponentSubschemeι Z)

/-- The scheme-theoretic closure of the complement of the chosen component. -/
noncomputable abbrev complementScheme
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk (schemeTheoreticClosureι (complement X Z) ≫ X.hom)

/-- The complementary closure inherits its structure morphism from the ambient scheme. -/
theorem complementScheme_spec
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (complementScheme X Z).hom = schemeTheoreticClosureι (complement X Z) ≫ X.hom := sorry

/-- The vanishing ideal sheaf of the chosen reduced component. -/
noncomputable def componentIdeal
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (X.left.irreducibleComponentClosed Z)

/-- The ideal sheaf defining the scheme-theoretic closure of the component complement. -/
noncomputable def complementIdeal
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : X.left.IdealSheafData :=
  schemeTheoreticClosureIdeal (complement X Z)

/-- The scheme-theoretic intersection of the component with its complementary closure. -/
noncomputable abbrev intersectionScheme
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : componentIdeal X Z ≤ componentIdeal X Z ⊔ complementIdeal X Z) ≫
      X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

/-- The intersection inherits its structure morphism through the component inclusion. -/
theorem intersectionScheme_spec
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (intersectionScheme X Z).hom =
      Scheme.IdealSheafData.inclusion
        (le_sup_left : componentIdeal X Z ≤ componentIdeal X Z ⊔ complementIdeal X Z) ≫
        X.left.irreducibleComponentSubschemeι Z ≫ X.hom := sorry

/-- The canonical inclusion of the intersection into the component. -/
noncomputable def intersectionToComponent
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (intersectionScheme X Z).left ⟶ (componentScheme X Z).left :=
  Scheme.IdealSheafData.inclusion
    (le_sup_left : componentIdeal X Z ≤ componentIdeal X Z ⊔ complementIdeal X Z)

/-- The canonical inclusion of the intersection into the complementary closure. -/
noncomputable def intersectionToComplement
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (intersectionScheme X Z).left ⟶ (complementScheme X Z).left :=
  Scheme.IdealSheafData.inclusion
    (le_sup_right : complementIdeal X Z ≤ componentIdeal X Z ⊔ complementIdeal X Z)

/-- The explicit algebra on global sections induced by a scheme morphism. -/
noncomputable abbrev sectionAlgebra
    {k : Type u} [Field k] (C D : SchemeOverField k) (i : D.left ⟶ C.left) :
    Algebra (Scheme.globalSectionsRing C.left) (Scheme.globalSectionsRing D.left) :=
  Scheme.Hom.globalSectionsAlgebra (i ≫ C.left.toSpecΓ)

/-- The rank of global sections over component sections with the morphism-induced scalar action. -/
noncomputable def sectionRank
    {k : Type u} [Field k] (C D : SchemeOverField k) (i : D.left ⟶ C.left) : ℕ :=
  @Module.finrank (Scheme.globalSectionsRing C.left) (Scheme.globalSectionsRing D.left)
    _ _ (sectionAlgebra C D i).toModule

/-- The section algebra sends a global function to its restriction along the scheme morphism. -/
theorem sectionAlgebra_map
    {k : Type u} [Field k] (C D : SchemeOverField k) (i : D.left ⟶ C.left) :
    @algebraMap (Scheme.globalSectionsRing C.left) (Scheme.globalSectionsRing D.left)
      _ _ (sectionAlgebra C D i) = i.appTop.hom := sorry

/-- Global sections of the target form a field and the source section algebra has degree two. -/
structure SectionDegreeTwo
    {k : Type u} [Field k] (C D : SchemeOverField k) (i : D.left ⟶ C.left) : Prop where
  /-- The target global-section ring is a field. -/
  base_isField : IsField (Scheme.globalSectionsRing C.left)
  /-- The source section algebra has rank two. -/
  degree : sectionRank C D i = 2

/-- Construct a degree-two section predicate from fieldness and the section rank. -/
def SectionDegreeTwo.ofMap
    {k : Type u} [Field k] (C D : SchemeOverField k) (i : D.left ⟶ C.left)
    (base_isField : IsField (Scheme.globalSectionsRing C.left))
    (degree : sectionRank C D i = 2) : SectionDegreeTwo C D i :=
  { base_isField := base_isField, degree := degree }

/-- A degree-two section predicate asserts both fieldness and rank two. -/
theorem SectionDegreeTwo.spec
    {k : Type u} [Field k] {C D : SchemeOverField k} {i : D.left ⟶ C.left}
    (h : SectionDegreeTwo C D i) :
    IsField (Scheme.globalSectionsRing C.left) ∧ sectionRank C D i = 2 := sorry

end RationalBridge

/-- A rational bridge is a selected irreducible component with nonempty complementary closure,
degree-two attachment over its section field, and genus zero. -/
structure RationalBridge {k : Type u} [Field k] (X : SchemeOverField k) where
  /-- The selected irreducible component. -/
  component : irreducibleComponents X.left
  /-- The scheme-theoretic complementary closure is nonempty. -/
  complement_nonempty : Nonempty (RationalBridge.complementScheme X component).left
  /-- The attachment has degree two over the component section field. -/
  sectionDegree : RationalBridge.SectionDegreeTwo
    (RationalBridge.componentScheme X component) (RationalBridge.intersectionScheme X component)
    (RationalBridge.intersectionToComponent X component)
  /-- The first structure-sheaf cohomology of the component vanishes. -/
  genus_zero : Scheme.Hom.cohomologyFinrank (RationalBridge.componentScheme X component).hom
    (SheafOfModules.unit (RationalBridge.componentScheme X component).left.ringCatSheaf :
      (RationalBridge.componentScheme X component).left.Modules) 1 = 0

namespace RationalBridge

/-- Construct a rational bridge from a component and its defining conditions. -/
def of
    {k : Type u} [Field k] (X : SchemeOverField k)
    (component : irreducibleComponents X.left)
    (complement_nonempty : Nonempty (complementScheme X component).left)
    (sectionDegree : SectionDegreeTwo (componentScheme X component)
      (intersectionScheme X component) (intersectionToComponent X component))
    (genus_zero : Scheme.Hom.cohomologyFinrank (componentScheme X component).hom
      (SheafOfModules.unit (componentScheme X component).left.ringCatSheaf :
        (componentScheme X component).left.Modules) 1 = 0) : RationalBridge X :=
  { component := component, complement_nonempty := complement_nonempty
    sectionDegree := sectionDegree, genus_zero := genus_zero }

/-- A rational bridge has a nonempty complementary closure and a genus-zero component,
together with its degree-two attachment predicate. -/
theorem spec
    {k : Type u} [Field k] {X : SchemeOverField k} (B : RationalBridge X) :
    (Nonempty (complementScheme X B.component).left ∧
      SectionDegreeTwo (componentScheme X B.component) (intersectionScheme X B.component)
        (intersectionToComponent X B.component)) ∧
      Scheme.Hom.cohomologyFinrank (componentScheme X B.component).hom
        (SheafOfModules.unit (componentScheme X B.component).left.ringCatSheaf :
          (componentScheme X B.component).left.Modules) 1 = 0 := sorry

/-- The attachment section algebra of a rational bridge has rank two. -/
theorem sectionDegree_spec
    {k : Type u} [Field k] {X : SchemeOverField k} (B : RationalBridge X) :
    sectionRank (componentScheme X B.component) (intersectionScheme X B.component)
      (intersectionToComponent X B.component) = 2 := sorry

variable {k : Type u} [Field k] (X : SchemeOverField k) [h_proper : IsProper X.hom]
  (h_dimension : topologicalKrullDim X.left = 1)
  (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
  (h_nodal : SchemeOverField.atWorstNodal X) (B : RationalBridge X)

include h_proper h_dimension hΓ h_nodal

/-- Every attachment point of a rational bridge on a proper nodal curve is an ambient node. -/
theorem intersection_isNode (p : (intersectionScheme X B.component).left) :
    SchemeOverField.isNode X
      (X.left.irreducibleComponentSubschemeι B.component
        (intersectionToComponent X B.component p)) := sorry

/-- Both the component and its complementary closure are smooth at every attachment point. -/
theorem intersection_smooth (p : (intersectionScheme X B.component).left) :
    (componentScheme X B.component).hom.SmoothAt (intersectionToComponent X B.component p) ∧
      (complementScheme X B.component).hom.SmoothAt
        (intersectionToComplement X B.component p) := sorry

/-- The component section field of a rational bridge on a proper nodal curve is finite separable
over the ground field, with the algebra induced by its structure morphism. -/
theorem componentSections_finite_separable :
    let componentAlgebra := Scheme.Hom.globalSectionsAlgebra (componentScheme X B.component).hom
    @Module.Finite k (Scheme.globalSectionsRing (componentScheme X B.component).left)
      _ _ componentAlgebra.toModule ∧
      @Algebra.IsSeparable k (Scheme.globalSectionsRing (componentScheme X B.component).left)
        _ _ componentAlgebra := sorry

/-- The attachment section algebra is either a separable quadratic field or the split product
of two copies of the component section field. -/
theorem intersectionSections_cases :
    let attachmentAlgebra := sectionAlgebra (componentScheme X B.component)
      (intersectionScheme X B.component) (intersectionToComponent X B.component)
    (IsField (Scheme.globalSectionsRing (intersectionScheme X B.component).left) ∧
      @Algebra.IsSeparable (Scheme.globalSectionsRing (componentScheme X B.component).left)
        (Scheme.globalSectionsRing (intersectionScheme X B.component).left)
        _ _ attachmentAlgebra) ∨
      Nonempty (@AlgEquiv (Scheme.globalSectionsRing (componentScheme X B.component).left)
        (Scheme.globalSectionsRing (intersectionScheme X B.component).left)
        (Scheme.globalSectionsRing (componentScheme X B.component).left ×
          Scheme.globalSectionsRing (componentScheme X B.component).left)
        _ _ _ attachmentAlgebra inferInstance) := sorry

end RationalBridge
end AlgebraicGeometry
