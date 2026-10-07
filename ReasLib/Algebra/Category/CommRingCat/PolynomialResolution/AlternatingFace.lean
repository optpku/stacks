module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Contraction.UnderlyingSet
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.AlternatingFace.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
@stack 08NA

# Alternating-face complex of a polynomial resolution

This leaf owns the chain-complex view and its quasi-isomorphic augmentation. Its proof-facing
criterion is the reusable module-view membership theorem from the underlying-set contraction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open AlgebraicTopology
open Under

universe u

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})

/-- The alternating-face chain complex of the polynomial resolution after forgetting to
`A`-modules, functorial in the resolved algebra. -/
@[stacks 08NA "polynomial resolution chain-complex functor"]
noncomputable abbrev complex : Under A ⥤ ChainComplex (ModuleCat.{u} A) ℕ :=
  underlying.moduleFunctor A ⋙
    (SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex (ModuleCat.{u} A))

/-- The canonical natural augmentation from the polynomial resolution complex to the underlying
`A`-module of the resolved algebra concentrated in degree zero. -/
@[stacks 08NA "polynomial resolution chain-complex augmentation"]
noncomputable def augmentation :
    complex A ⟶ underlying.moduleFunctor A ⋙
      (SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ (ModuleCat.{u} A)) :=
  Functor.whiskerLeft (underlying.moduleFunctor A) AlternatingFaceMapComplex.ε

/-- The component of the canonical polynomial-resolution chain-complex augmentation at `B`. -/
@[simp, stacks 08NA "polynomial resolution augmentation component"]
theorem augmentation.app (B : Under A) :
    (augmentation A).app B = AlternatingFaceMapComplex.ε.app (underlying.module A B) := sorry

/-- The canonical polynomial-resolution augmentation is pointwise a quasi-isomorphism as a
natural transformation of chain-complex-valued functors. -/
@[stacks 08NA "polynomial augmentation in the pointwise quasi-isomorphism property"]
theorem augmentation.mem_quasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A)
      (ComplexShape.down ℕ)).functorCategory (Under A) (augmentation A) := sorry

/-- Every component of the canonical polynomial-resolution chain-complex augmentation is a
quasi-isomorphism. -/
@[stacks 08NA "polynomial resolution alternating-face quasi-isomorphism"]
instance augmentation.quasiIso (B : Under A) :
    QuasiIso ((augmentation A).app B) := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
