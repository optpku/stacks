module

import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FlatBaseChange
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.5.2 (Flat base change): for a cartesian square of schemes with flat base morphism
and quasi-compact, quasi-separated vertical morphism, pullback identifies every higher direct
image of a quasicoherent module with the higher direct image of its pullback. -/
@[stacks 02KH] #check
  (AlgebraicGeometry.Scheme.flatBaseChange_pullback_higherDirectImage_isomorphic :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (sq : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ),
      IsIsomorphic
        ((Scheme.Modules.pullback g).obj
          (higherDirectImageModule f.toShHom ℱ i))
        (higherDirectImageModule f'.toShHom
          ((Scheme.Modules.pullback g').obj ℱ) i))

/- Over affine bases, the same comparison is extension of scalars on canonical cohomology
modules. -/
#check
  (AlgebraicGeometry.Scheme.Hom.cohomology_baseChange_of_flat :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X Y : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A))
      (g : Y ⟶ Spec (CommRingCat.of B))
      (h : Y ⟶ X)
      (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
      [Module.Flat A B] [QuasiCompact f] [QuasiSeparated f]
      (F : X.Modules) [F.IsQuasicoherent] (i : ℕ),
      IsIsomorphic
        ((ModuleCat.extendScalars (algebraMap A B)).obj
          (AlgebraicGeometry.Scheme.Hom.cohomology f F i))
        (AlgebraicGeometry.Scheme.Hom.cohomology g
          ((Scheme.Modules.pullback h).obj F) i))
