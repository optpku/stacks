module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty.Descent

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable morphism of algebraic spaces has a scheme-morphism property
if and only if its represented pullback along a surjective étale atlas has that property. -/
theorem representableMorphismProperty_iff_atlas_snd {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] {f : G ⟶ F}
    (hf : yoneda.relativelyRepresentable f) {U : Over S}
    (q : yoneda.obj U ⟶ F.functorOfPoints)
    (hq_etale : (over (@Etale)).presheaf q)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q) :
    Scheme.representableMorphismProperty S P f ↔ P (hf.snd q).left := sorry

end AlgebraicGeometry.AlgebraicSpace
