module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport
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

#check (AlgebraicGeometry.Scheme.Etale.HasCompactSupport :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    F.obj.obj (op (globalEtale X.left)) → Prop)

#check (AlgebraicGeometry.Scheme.Etale.hasCompactSupport_iff :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))),
    HasCompactSupport F σ ↔
      ClosedSubset.IsProperOver X.hom
        (abelianSheafSectionSupport F (globalEtale X.left) σ))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupport :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    Set (F.obj.obj (op (globalEtale X.left))))

#check (AlgebraicGeometry.Scheme.Etale.mem_globalSectionsCompactSupport_iff :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))),
    σ ∈ globalSectionsCompactSupport F ↔ HasCompactSupport F σ)

end AlgebraicGeometry.Scheme.Etale

end
