/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory.MorphismProperty

/-- In a commutative square of schemes, source-locus membership is preserved and
reflected when the target map is smooth at the marked image and the canonical
comparison to the pullback is étale at the marked point. -/
theorem mem_sourceLocus_iff_of_smoothAt_etaleComparison
    (P : MorphismProperty Scheme.{u}) [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget Scheme.bigSmoothPrecoverage]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (g : Y' ⟶ Y) (f : X ⟶ Y) (sq : CommSq f' g' g f) (x' : X')
    (hg : g.SmoothAt (f' x'))
    (hcomp : (pullback.lift g' f' sq.w.symm).EtaleAt x') :
    g' x' ∈ P.sourceLocus f ↔ x' ∈ P.sourceLocus f' := sorry

end CategoryTheory.MorphismProperty
