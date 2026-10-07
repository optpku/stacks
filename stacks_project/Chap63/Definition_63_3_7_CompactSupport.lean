module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology

/-!
# Compactly supported global étale sections

Underived `H^0_c(X, F)` is the set of global small-étale sections whose
support is proper over the base field.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] {X : SchemeOverField k}

/-- A global étale section has compact support when its étale section support is
proper over the base field. -/
def HasCompactSupport [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) : Prop :=
  ClosedSubset.IsProperOver X.hom
    (abelianSheafSectionSupport F (globalEtale X.left) σ)

/-- Compact support of a global étale section is properness of its étale section
support over the base field. -/
theorem hasCompactSupport_iff [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    HasCompactSupport F σ ↔
      ClosedSubset.IsProperOver X.hom
        (abelianSheafSectionSupport F (globalEtale X.left) σ) :=
  sorry

/-- The set `H^0_c(X, F) ⊂ H^0(X, F)` of global étale sections with compact
support. -/
def globalSectionsCompactSupport [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Set (F.obj.obj (op (globalEtale X.left))) :=
  {σ | HasCompactSupport F σ}

/-- Membership in compactly supported global étale sections is compact support of
the section. -/
theorem mem_globalSectionsCompactSupport_iff
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    σ ∈ globalSectionsCompactSupport F ↔ HasCompactSupport F σ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
