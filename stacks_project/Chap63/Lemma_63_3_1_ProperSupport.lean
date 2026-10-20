module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProperSupport
public import stacks_project.Chap59.Lemma_59_79_1_DirectImage

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A direct-image section has proper support over an étale base object precisely
when its closed section support is proper over that object. -/
abbrev HasProperSupportOver {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : ((etaleDirectImage f).obj F).1.obj (op V)) : Prop :=
  HasProperSupport f F V σ

#check (HasProperSupportOver :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (_ : ((etaleDirectImage f).obj F).1.obj (op V)), Prop)

#check (properSupportSections :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale),
    AddSubgroup (((etaleDirectImage f).obj F).1.obj (op V)))

#check (properSupportSubfunctor :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    Subfunctor (((etaleDirectImage f).obj F).obj ⋙ CategoryTheory.forget AddCommGrpCat))

end AlgebraicGeometry.Scheme.Etale

end
