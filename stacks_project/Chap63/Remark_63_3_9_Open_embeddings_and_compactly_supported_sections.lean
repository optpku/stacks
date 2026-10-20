module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    globalSectionsCompactSupportSubgroup X'
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F)

/- Remark 63.3.9 (Open embeddings and compactly supported sections): extension
by zero along an open immersion induces an injective map on compactly
supported global sections. -/
@[stacks 0F74]
#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportOpenImmersion_injective :
  ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    Function.Injective (globalSectionsCompactSupportOpenImmersion j F))

#check (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportCopresheaf :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    X.left.Opens ⥤ AddCommGrpCat.{u})

end
