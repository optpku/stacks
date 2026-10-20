module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import stacks_project.Chap59.Lemma_59_54_1

/-!
# Composition of compact-support étale direct images

The canonical comparison maps and sectionwise image for iterated direct image
with proper support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale

#check (AlgebraicGeometry.Scheme.Etale.smallEtalePullbackCompIso :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g))

#check (AlgebraicGeometry.Scheme.Etale.etaleAbelianPushforwardCompIso :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    etaleAbelianPushforward f ⋙ etaleAbelianPushforward g ≅
      etaleAbelianPushforward (f ≫ g))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompι :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g],
    etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleAbelianPushforward (f ≫ g))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompι_app :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleLowerShriekCompι f g).app F =
      (etaleLowerShriekι g).app ((etaleLowerShriek f).obj F) ≫
        (etaleAbelianPushforward g).map ((etaleLowerShriekι f).app F) ≫
        (etaleAbelianPushforwardCompIso f g).hom.app F)

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompSections :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale),
    AddSubgroup (F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))))

#check (AlgebraicGeometry.Scheme.Etale.mem_etaleLowerShriekCompSections_iff :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))),
    σ ∈ etaleLowerShriekCompSections f g F W ↔
      ∃ τ : compactSupportSections g ((etaleLowerShriek f).obj F) W,
        ((etaleLowerShriekCompι f g).app F).hom.app (op W) τ = σ)

end AlgebraicGeometry.Scheme.Etale

end
