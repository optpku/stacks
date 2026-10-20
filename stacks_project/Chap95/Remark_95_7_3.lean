module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Descent
import StacksCheckRecall

/-!
# Remark 95.7.3

Along a small-index fppf covering family in `(Sch/S)_fppf`, the fibre
pseudofunctor of `p : Spaces ⥤ Over S` has essentially surjective descent.
The informal instruction to ignore the set-theoretic hypothesis of Bootstrap,
Lemma 80.11.1, is recorded as `[Small.{u} I]` on the chosen covering index,
not as an unconditional `IsStack.OnSite` instance.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/- Remark 95.7.3: ignoring set-theoretic size, recorded as `[Small.{u} I]` on the
chosen covering index as in Bootstrap, Lemma 80.11.1, `Spaces` satisfies descent
for objects along an fppf covering `{Ui i ⟶ U}` in `(Sch/S)_fppf`. Equivalently,
`(fiberPseudofunctor p).toDescentData f` is essentially surjective, so a family
of algebraic spaces over the `Ui i` with cocycle isomorphisms over the fibre
products `Ui i ×_U Ui j` arises from some object of `p.Fiber U`. -/
@[stacks 04UB] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.essSurj_ofArrows :
  ∀ {S : Scheme.{u}} {U : Over S}
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U),
    ((Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).toDescentData f).EssSurj)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.isStackFor_ofArrows :
  ∀ {S : Scheme.{u}} {U : Over S}
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U),
    (Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).IsStackFor
      (Presieve.ofArrows Ui f))

end AlgebraicGeometry.AlgebraicSpace.Spaces
