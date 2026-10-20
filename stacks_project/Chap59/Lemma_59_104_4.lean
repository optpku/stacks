module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/- Lemma 59.104.4 (1): let `f : X ⟶ Y` be a morphism of schemes and let `g : Z ⟶ Y`
be a surjective integral morphism. If the functors from Type-valued sheaves on
`Z.smallEtaleTopology` to singleton descent data along `{pullback.snd f g : X ×_Y Z ⟶ Z}`
and from Type-valued sheaves on `(Z ×_Y Z).smallEtaleTopology` to singleton descent
data along `{pullback.snd f (pullback.fst g g ≫ g) : X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}`
are equivalences of categories, then the functor from Type-valued sheaves on
`Y.smallEtaleTopology` to singleton descent data along `{f : X ⟶ Y}` is an
equivalence. -/
@[stacks 0GF1]
#check (AlgebraicGeometry.Scheme.EtaleSheaf.descentIsEquivalenceOfBaseChangeOfSurjectiveIntegral :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [IsIntegralHom g]
    (hZ : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ pullback.snd f g)).IsEquivalence)
    (hZZ : (pseudofunctor.toDescentData
        (fun _ : PUnit.{1} ↦ pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence),
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence)

/- Lemma 59.104.4 (2): let `f : X ⟶ Y` be a morphism of schemes and let `g : Z ⟶ Y`
be a surjective proper morphism. If the functors from Type-valued sheaves on
`Z.smallEtaleTopology` to singleton descent data along `{pullback.snd f g : X ×_Y Z ⟶ Z}`
and from Type-valued sheaves on `(Z ×_Y Z).smallEtaleTopology` to singleton descent
data along `{pullback.snd f (pullback.fst g g ≫ g) : X ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z}`
are equivalences of categories, then the functor from Type-valued sheaves on
`Y.smallEtaleTopology` to singleton descent data along `{f : X ⟶ Y}` is an
equivalence. -/
@[stacks 0GF1]
#check (AlgebraicGeometry.Scheme.EtaleSheaf.descentIsEquivalenceOfBaseChangeOfSurjectiveProper :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [IsProper g]
    (hZ : (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ pullback.snd f g)).IsEquivalence)
    (hZZ : (pseudofunctor.toDescentData
        (fun _ : PUnit.{1} ↦ pullback.snd f (pullback.fst g g ≫ g))).IsEquivalence),
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence)

end AlgebraicGeometry.Scheme.EtaleSheaf
