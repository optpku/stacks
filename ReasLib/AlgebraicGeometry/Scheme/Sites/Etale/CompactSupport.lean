module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections

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
        (abelianSheafSectionSupport F (globalEtale X.left) σ) := Iff.rfl

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
    σ ∈ globalSectionsCompactSupport F ↔ HasCompactSupport F σ := Iff.rfl

/-- Every global étale section of an abelian sheaf on a scheme proper over a field
has compact support. -/
theorem hasCompactSupport_of_isProper [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    HasCompactSupport F σ := sorry

/-- The compactly supported global sections of an abelian étale sheaf on a scheme
proper over a field are all its global sections. -/
theorem globalSectionsCompactSupport_eq_univ [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupport F = Set.univ := sorry

/-- The zero global étale section has compact support. -/
theorem hasCompactSupport_zero [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    HasCompactSupport F 0 := by
  sorry

/-- The sum of two compactly supported global étale sections has compact support. -/
theorem hasCompactSupport_add [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    {σ τ : F.obj.obj (op (globalEtale X.left))}
    (hσ : HasCompactSupport F σ) (hτ : HasCompactSupport F τ) :
    HasCompactSupport F (σ + τ) := by
  sorry

/-- The negative of a compactly supported global étale section has compact support. -/
theorem hasCompactSupport_neg [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    {σ : F.obj.obj (op (globalEtale X.left))} (hσ : HasCompactSupport F σ) :
    HasCompactSupport F (-σ) := by
  sorry

/-- The additive subgroup `H^0_c(X, F)` of global étale sections with compact
support. -/
def globalSectionsCompactSupportSubgroup (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    AddSubgroup (F.obj.obj (op (globalEtale X.left))) where
  carrier := globalSectionsCompactSupport F
  zero_mem' := hasCompactSupport_zero F
  add_mem' := fun hσ hτ => hasCompactSupport_add F hσ hτ
  neg_mem' := fun hσ => hasCompactSupport_neg F hσ

/-- Membership in the compactly supported global-section subgroup is compact
support of the section. -/
theorem mem_globalSectionsCompactSupportSubgroup_iff (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))) :
    σ ∈ globalSectionsCompactSupportSubgroup X F ↔ HasCompactSupport F σ :=
  Iff.rfl

/-- A sheaf isomorphism preserves compact support of global étale sections. -/
private theorem mem_globalSectionsCompactSupportSubgroup_mapIso (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G)
    (σ : globalSectionsCompactSupportSubgroup X F) :
    (α.hom.hom.app (op (globalEtale X.left)))
        ((globalSectionsCompactSupportSubgroup X F).subtype σ) ∈
      globalSectionsCompactSupportSubgroup X G :=
  sorry

/-- The map on compactly supported global sections induced by an isomorphism of
abelian étale sheaves. -/
def globalSectionsCompactSupportMapIso (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G) :
    globalSectionsCompactSupportSubgroup X F →+
      globalSectionsCompactSupportSubgroup X G :=
  (((α.hom.hom.app (op (globalEtale X.left))).hom.comp
        (globalSectionsCompactSupportSubgroup X F).subtype).codRestrict
    (globalSectionsCompactSupportSubgroup X G)
    (by exact mem_globalSectionsCompactSupportSubgroup_mapIso X α))

/-- Transport of a compactly supported section evaluates by the sheaf isomorphism. -/
theorem globalSectionsCompactSupportMapIso_apply (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G)
    (σ : globalSectionsCompactSupportSubgroup X F) :
    (globalSectionsCompactSupportMapIso X α σ).val =
      α.hom.hom.app (op (globalEtale X.left)) σ.val := rfl

/-- The inclusion of compactly supported global étale sections into all global
sections is bijective when the scheme is proper over the base field. -/
theorem globalSectionsCompactSupportSubgroup_subtype_bijective
    {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (globalSectionsCompactSupportSubgroup X F).subtype :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
