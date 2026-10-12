/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleAtlas
import StacksCheckRecall

/-!
# Representable morphisms from étale atlas pullbacks

A map of fppf sheaves into an algebraic space that becomes representable with property `P`
after pullback along a surjective étale atlas is itself representable with property `P`,
provided `P` is stable under base change, fppf-local on the target, and satisfies fppf
descent. The source sheaf is then an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.11.5: let `S` be a scheme, let `a : G ⟶ F.functorOfPoints` be a
transformation of presheaves on `(Sch/S)_fppf`, and let `P` be a property of morphisms
of schemes that is stable under base change, fppf local on the target, and satisfies
descent for fppf coverings in the sense of `P.SatisfiesDescent DescentTopology.fppf`.
Assume `G` is an fppf sheaf, `F` is an algebraic space, and there is a scheme `U` over
`S` with a surjective étale morphism `q : yoneda.obj U ⟶ F.functorOfPoints` such that
the fibre product `V = G ×_F U` is representable and `V ⟶ U` has property `P`. Then
`a` is representable and has property `P`; `G` is an algebraic space via
`AlgebraicSpace.ofRelativelyRepresentable` applied to the representability conclusion. -/
@[stacks 03I2] #check (AlgebraicGeometry.AlgebraicSpace.representable_of_etale_atlas :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (a : G ⟶ F.functorOfPoints) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hP : P.SatisfiesDescent DescentTopology.fppf) {U : Over S}
    (q : yoneda.obj U ⟶ F.functorOfPoints) (hq_etale : (over (@Etale)).presheaf q)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
    {V : Over S} (fst : yoneda.obj V ⟶ G) (snd : V ⟶ U)
    (hV : IsPullback fst (yoneda.map snd) a q) (hsnd : P snd.left),
    (over P).presheaf a)
