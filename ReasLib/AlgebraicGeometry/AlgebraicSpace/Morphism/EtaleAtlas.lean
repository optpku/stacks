/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OfRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

/-!
# Representability from étale atlas pullbacks

Effective fppf descent for a scheme-morphism property allows representability and
that property to descend from a surjective étale atlas of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A transformation from an fppf sheaf to an algebraic space is representable with
property `P` if its pullback along a surjective étale atlas is represented by a scheme
whose structure morphism has `P`, provided `P` is stable under base change, fppf-local
on the target, and satisfies effective fppf descent. Its source is consequently an
algebraic space via `ofRelativelyRepresentable`. -/
theorem representable_of_etale_atlas {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (a : G ⟶ F.functorOfPoints) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : P.SatisfiesDescent DescentTopology.fppf) {U : Over S}
    (q : yoneda.obj U ⟶ F.functorOfPoints) (hq_etale : (over (@Etale)).presheaf q)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    {V : Over S} (fst : yoneda.obj V ⟶ G) (snd : V ⟶ U)
    (hV : IsPullback fst (yoneda.map snd) a q) (hsnd : P snd.left) :
    (over P).presheaf a := sorry

end AlgebraicGeometry.AlgebraicSpace
