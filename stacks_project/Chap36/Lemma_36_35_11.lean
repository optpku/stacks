module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.PseudoCoherentDual
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent

@[expose] public section

open CategoryTheory
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.35.11: for a proper flat morphism of finite presentation over a
quasi-compact and quasi-separated scheme, the pushforward of the internal Hom from a
pseudo-coherent complex to a relatively perfect complex is the dual of a pseudo-coherent
complex, and the same choice of complex gives this description after every cartesian base
change. -/
@[stacks 0DJU] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_pseudoCoherent_dual :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      (E K : RingedSpace.ModuleDerived X.toRingedSpace),
      IsPerfectRelativeTo f E →
        RingedSpace.ModuleDerived.IsPseudoCoherent K →
          ∃ L : RingedSpace.ModuleDerived S.toRingedSpace,
            RingedSpace.ModuleDerived.IsPseudoCoherent L ∧
              IsIsomorphic
                ((RingedSpace.moduleDerivedPushforward f.toShHom).obj (K ⟹ E))
                (MonoidalClosed.dual L) ∧
              ∀ {X' S' : Scheme.{u}}
                [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
                [MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace)]
                [MonoidalCategory (RingedSpace.ModuleDerived S'.toRingedSpace)]
                [MonoidalClosed (RingedSpace.ModuleDerived S'.toRingedSpace)]
                (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
                IsPullback g' f' f g →
                  IsIsomorphic
                    ((RingedSpace.moduleDerivedPushforward f'.toShHom).obj
                      ((RingedSpace.modulePullbackDerived g'.toShHom).obj K ⟹
                        (RingedSpace.modulePullbackDerived g'.toShHom).obj E))
                    (MonoidalClosed.dual
                      ((RingedSpace.modulePullbackDerived g.toShHom).obj L)))

end AlgebraicGeometry.Scheme.ModuleDerived
