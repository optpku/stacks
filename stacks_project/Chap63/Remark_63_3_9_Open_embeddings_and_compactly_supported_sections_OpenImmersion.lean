module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap63.Definition_63_3_7_CompactSupport
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.OpenImmersion

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportSubgroup :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    AddSubgroup (F.obj.obj (op (globalEtale X.left))))

#check (AlgebraicGeometry.Scheme.Etale.mem_globalSectionsCompactSupportSubgroup_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.obj.obj (op (globalEtale X.left))),
    σ ∈ globalSectionsCompactSupportSubgroup X F ↔ HasCompactSupport F σ)

#check (AlgebraicGeometry.Scheme.Etale.globalEtaleOpenImmersion :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k} (j : X' ⟶ X)
    [IsOpenImmersion j.left],
    (etaleRestriction j.left).obj (globalEtale X'.left) ⟶ globalEtale X.left)

#check (AlgebraicGeometry.Scheme.Etale.extendGlobalCompactSupportSection :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)),
    F.obj.obj (op (globalEtale X.left)))

#check (AlgebraicGeometry.Scheme.Etale.hasCompactSupport_extendGlobalCompactSupportSection :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)),
    HasCompactSupport F (extendGlobalCompactSupportSection j F σ))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    globalSectionsCompactSupportSubgroup X'
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F)

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_apply :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)),
    (globalSectionsCompactSupportOpenImmersion j F σ).val =
      extendGlobalCompactSupportSection j F σ)

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_injective :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    Function.Injective (globalSectionsCompactSupportOpenImmersion j F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_restrict :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)),
    F.obj.map (globalEtaleOpenImmersion j).op
        (extendGlobalCompactSupportSection j F σ) =
      (globalSectionsCompactSupportSubgroup X'
          ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ)

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_id :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    globalSectionsCompactSupportOpenImmersion (𝟙 X) F =
      AddMonoidHom.id (globalSectionsCompactSupportSubgroup X F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportMapIso :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    {F G : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}} (α : F ≅ G),
    globalSectionsCompactSupportSubgroup X F →+
      globalSectionsCompactSupportSubgroup X G)

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_comp :
  ∀ {k : Type u} [Field k] {X X' X'' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom]
    [IsSeparated X''.hom] [LocallyOfFiniteType X''.hom]
    (j : X' ⟶ X) (j' : X'' ⟶ X') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    (globalSectionsCompactSupportOpenImmersion j F).comp
        ((globalSectionsCompactSupportOpenImmersion j'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).comp
          (globalSectionsCompactSupportMapIso X''
            ((etaleAbelianRestrictionSheafCompIso j.left j'.left).symm.app F))) =
      globalSectionsCompactSupportOpenImmersion (j' ≫ j) F)

#check (AlgebraicGeometry.Scheme.Etale.etaleRestrictionSheaf_opensLe :
  ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.Opens} (h : U ≤ V),
    (etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F ≅
      (etaleRestrictionSheaf (X.homOfLE h) AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpensHom :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.left.Opens}
    (h : U ≤ V),
    globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X V)
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpens :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (U : X.left.Opens),
    globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F)

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportCopresheaf :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    X.left.Opens ⥤ AddCommGrpCat.{u})

end
