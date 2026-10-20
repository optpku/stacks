module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Separated
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 63.4.1: For a separated locally quasi-finite morphism, the finite-support
presheaf is canonically naturally isomorphic to the underlying compact-support sheaf. -/
@[stacks 0F6N] #check
  (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f]
      [LocallyOfFiniteType f],
      AlgebraicGeometry.Scheme.Etale.lowerShriekPresheaf f ≅
        AlgebraicGeometry.Scheme.Etale.etaleLowerShriek f ⋙
          sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u})
