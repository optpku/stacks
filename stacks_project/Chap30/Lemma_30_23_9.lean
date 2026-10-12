/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

/- Lemma 30.23.9: for a morphism `f : X ⟶ Y` of Noetherian schemes and ideal-sheaf data
`J` on `Y`, stagewise pullback gives a right exact functor from coherent formal modules along `J`
to coherent formal modules along `J.comap f`; when `f` is flat, such a functor is exact. -/
@[stacks 0887] #check
  (AlgebraicGeometry.Scheme.coherentFormalModules_pullback_exists_rightExact :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) (J : Y.IdealSheafData),
      ∃ F : AlgebraicGeometry.Scheme.CoherentFormalModules Y J ⥤
          AlgebraicGeometry.Scheme.CoherentFormalModules X (J.comap f),
        AlgebraicGeometry.Scheme.IsCoherentFormalModulesPullbackFunctor f J F ∧
          rightExactFunctor (AlgebraicGeometry.Scheme.CoherentFormalModules Y J)
            (AlgebraicGeometry.Scheme.CoherentFormalModules X (J.comap f)) F)

#check
  (AlgebraicGeometry.Scheme.isCoherentFormalModulesPullbackFunctor_spec :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
      (F : AlgebraicGeometry.Scheme.CoherentFormalModules Y J ⥤
        AlgebraicGeometry.Scheme.CoherentFormalModules X (J.comap f))
      (hF : AlgebraicGeometry.Scheme.IsCoherentFormalModulesPullbackFunctor f J F),
      (∀ (M : AlgebraicGeometry.Scheme.CoherentFormalModules Y J) (n : ℕ),
        (((F.obj M).obj).obj (op n)).obj =
          (AlgebraicGeometry.Scheme.Modules.pullback f).obj (((M.obj).obj (op n)).obj)) ∧
        (∀ (M : AlgebraicGeometry.Scheme.CoherentFormalModules Y J)
          {i j : ℕ} (hij : i ≤ j),
          ((((F.obj M).obj).transitionMap hij).hom) =
            eqToHom (hF.obj_eq M j) ≫
              (AlgebraicGeometry.Scheme.Modules.pullback f).map
                (((M.obj).transitionMap hij).hom) ≫
              eqToHom (hF.obj_eq M i).symm) ∧
          ∀ {M N : AlgebraicGeometry.Scheme.CoherentFormalModules Y J} (g : M ⟶ N) (n : ℕ),
            ((F.map g).hom.app (op n)).hom =
              eqToHom (hF.obj_eq M n) ≫
                (AlgebraicGeometry.Scheme.Modules.pullback f).map
                  ((g.hom.app (op n)).hom) ≫
                eqToHom (hF.obj_eq N n).symm)

#check
  (AlgebraicGeometry.Scheme.coherentFormalModules_pullback_exact_of_flat :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
      (F : AlgebraicGeometry.Scheme.CoherentFormalModules Y J ⥤
        AlgebraicGeometry.Scheme.CoherentFormalModules X (J.comap f))
      (hF : AlgebraicGeometry.Scheme.IsCoherentFormalModulesPullbackFunctor f J F),
      exactFunctor (AlgebraicGeometry.Scheme.CoherentFormalModules Y J)
        (AlgebraicGeometry.Scheme.CoherentFormalModules X (J.comap f)) F)
