module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Kernel pairs of algebraic space atlases

This module records the represented kernel pair `R = U ×_F U` of a relatively
representable morphism from a scheme to an algebraic space, as a pre-relation on
`U` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The represented kernel pair `R = U ×_F U` of a relatively representable morphism
`f : U ⟶ F` from a scheme to an algebraic space, as a pre-relation on `U` over `S`. -/
def kernelPair {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    Scheme.PreRelation U :=
  Scheme.PreRelation.ofHom (prod.lift (hf.fst' f) (hf.snd f))

/-- The structure morphism of `kernelPair f hf` is the product lift of the two projections
of the represented pullback of `f` along itself. -/
theorem kernelPair_hom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    (kernelPair f hf).hom = prod.lift (hf.fst' f) (hf.snd f) := sorry

/-- The first projection of `kernelPair f hf` is the represented first projection of the
pullback of `f` along itself. -/
theorem kernelPair_t {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    (kernelPair f hf).t = hf.fst' f := sorry

/-- The second projection of `kernelPair f hf` is the represented second projection of the
pullback of `f` along itself. -/
theorem kernelPair_s {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    (kernelPair f hf).s = hf.snd f := sorry

/-- The two projections of `kernelPair f hf` form the kernel pair of `f` in the presheaf
category. -/
theorem isKernelPair {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    IsKernelPair f (yoneda.map (kernelPair f hf).t) (yoneda.map (kernelPair f hf).s) :=
  sorry

/-- `T`-valued points of the kernel pair are pairs of `T`-valued points of `U` on which `f`
agrees. -/
theorem pointRel_iff {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f)
    (T : Over S) (x y : T ⟶ U) :
    (kernelPair f hf).pointRel T x y ↔ yoneda.map x ≫ f = yoneda.map y ≫ f := sorry

end AlgebraicGeometry.AlgebraicSpace
