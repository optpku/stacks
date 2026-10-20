module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The pretriangulation determined by admissible cones

An explicit family of admissible cones determines the distinguished triangles in the homotopy
category. The distinguished set is concrete data; the pretriangulated axioms are exposed as
separate proof obligations before they are assembled into a `Pretriangulated` structure.
-/

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasShift (K R A) ℤ]
variable [(Comp.inKFunctor : Comp R A ⥤ K R A).CommShift ℤ]

namespace CompBoundaryAssignment.AdmissibleCones

/-- The triangles isomorphic to a triangle arising from the explicit cone family `C`. -/
def distinguishedTrianglesInK (C : B.AdmissibleCones) : Set (Triangle (K R A)) :=
  { T | ∃ (x y : Comp R A) (f : x ⟶ y), Nonempty (T ≅ (C.cone f).triangleInK) }

namespace distinguishedTrianglesInK

/-- Membership means being isomorphic to a triangle supplied by the explicit cone family. -/
theorem mem_iff (C : B.AdmissibleCones) {T : Triangle (K R A)} :
    T ∈ C.distinguishedTrianglesInK ↔
      ∃ (x y : Comp R A) (f : x ⟶ y), Nonempty (T ≅ (C.cone f).triangleInK) := sorry

/-- Every triangle supplied by the explicit cone family belongs to its distinguished set. -/
@[simp] theorem cone_mem (C : B.AdmissibleCones) {x y : Comp R A} (f : x ⟶ y) :
    (C.cone f).triangleInK ∈ C.distinguishedTrianglesInK := sorry

/-- The distinguished set is closed under transport along triangle isomorphisms. -/
theorem isomorphic_mem (C : B.AdmissibleCones)
    (T₁ : Triangle (K R A)) (hT₁ : T₁ ∈ C.distinguishedTrianglesInK)
    (T₂ : Triangle (K R A)) (e : T₂ ≅ T₁) :
    T₂ ∈ C.distinguishedTrianglesInK := sorry

section PretriangulatedAxioms

variable [Limits.HasZeroObject (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]

/-- Contractible triangles belong to the distinguished set. -/
theorem contractible_mem (C : B.AdmissibleCones) (X : K R A) :
    contractibleTriangle X ∈ C.distinguishedTrianglesInK := sorry

/-- Every morphism in the homotopy category extends to a triangle in the distinguished set. -/
theorem exists_cocone (C : B.AdmissibleCones) {X Y : K R A} (f : X ⟶ Y) :
    ∃ (Z : K R A) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ C.distinguishedTrianglesInK := sorry

/-- Membership in the distinguished set is invariant under triangle rotation. -/
theorem rotate_mem_iff (C : B.AdmissibleCones) (T : Triangle (K R A)) :
    T ∈ C.distinguishedTrianglesInK ↔ T.rotate ∈ C.distinguishedTrianglesInK := sorry

/-- A commutative square between triangles in the distinguished set extends to their third
objects. -/
theorem exists_morphism (C : B.AdmissibleCones)
    (T₁ T₂ : Triangle (K R A))
    (hT₁ : T₁ ∈ C.distinguishedTrianglesInK) (hT₂ : T₂ ∈ C.distinguishedTrianglesInK)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
      T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := sorry

end PretriangulatedAxioms

end distinguishedTrianglesInK

variable [Limits.HasZeroObject (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]

/-- Lemma 22.27.14 (09QW): the pretriangulation of `K R A` determined by the explicit
admissible-cone family `C`. -/
@[reducible, stacks 09QW]
noncomputable def pretriangulated (C : B.AdmissibleCones) : Pretriangulated (K R A) where
  distinguishedTriangles := C.distinguishedTrianglesInK
  isomorphic_distinguished := distinguishedTrianglesInK.isomorphic_mem C
  contractible_distinguished := distinguishedTrianglesInK.contractible_mem C
  distinguished_cocone_triangle := distinguishedTrianglesInK.exists_cocone C
  rotate_distinguished_triangle := distinguishedTrianglesInK.rotate_mem_iff C
  complete_distinguished_triangle_morphism := distinguishedTrianglesInK.exists_morphism C

/-- An explicit cone family is compatible with a pretriangulation when all of its associated
triangles belong to that pretriangulation's distinguished set. -/
@[stacks 09QW "cone triangles are distinguished"]
def TrianglesDistinguished (C : B.AdmissibleCones) (P : Pretriangulated (K R A)) : Prop :=
  ∀ {x y : Comp R A} (f : x ⟶ y),
    (C.cone f).triangleInK ∈ P.distinguishedTriangles

/-- An admissible-cone system presents a pretriangulation when its isomorphism-closed cone
triangles are exactly the distinguished triangles of that pretriangulation. -/
@[stacks 09QW "admissible cones present a pretriangulation"]
def Presents (C : B.AdmissibleCones) (P : Pretriangulated (K R A)) : Prop :=
  P.distinguishedTriangles = C.distinguishedTrianglesInK

/-- The cone triangles are distinguished in the pretriangulation constructed from `C`. -/
@[stacks 09QW "cone triangles in the induced pretriangulation"]
theorem trianglesDistinguishedInK (C : B.AdmissibleCones) :
    C.TrianglesDistinguished (C.pretriangulated) := sorry

/-- The pretriangulation constructed from an admissible-cone system is presented by that
system. -/
@[stacks 09QW "presentation of the induced pretriangulation"]
theorem presentsPretriangulated (C : B.AdmissibleCones) :
    C.Presents C.pretriangulated := sorry

end CompBoundaryAssignment.AdmissibleCones

end DifferentialGradedCategory

open DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones
