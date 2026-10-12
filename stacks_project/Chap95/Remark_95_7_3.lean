/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Lemma_95_7_2
public import ReasLib.CategoryTheory.Sites.Descent.Basic

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

/-- Remark 95.7.3: ignoring set-theoretic size, recorded as `[Small.{u} I]` on the
chosen covering index as in Bootstrap, Lemma 80.11.1, `Spaces` satisfies descent
for objects along an fppf covering `{Ui i ⟶ U}` in `(Sch/S)_fppf`. Equivalently,
`(fiberPseudofunctor p).toDescentData f` is essentially surjective, so a family
of algebraic spaces over the `Ui i` with cocycle isomorphisms over the fibre
products `Ui i ×_U Ui j` arises from some object of `p.Fiber U`. -/
@[stacks 04UB]
theorem essSurj_ofArrows {S : Scheme.{u}} {U : Over S}
    [IsPrestack.OnSite (Scheme.fppfTopology.over S) (p : Spaces S ⥤ Over S)]
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U) :
    ((Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).toDescentData f).EssSurj :=
  sorry

/-- Essential surjectivity of the descent functor unpacks as existence of a fibre
object over `U` whose canonical descent data is isomorphic to the given datum. -/
theorem exists_iso_of_descentData {S : Scheme.{u}} {U : Over S}
    [IsPrestack.OnSite (Scheme.fppfTopology.over S) (p : Spaces S ⥤ Over S)]
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U)
    (D : (Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).DescentData f) :
    ∃ X : p.Fiber U,
      Nonempty (((Functor.fiberPseudofunctor p).toDescentData f).obj X ≅ D) :=
  sorry

/-- Covering-level stack condition for `Spaces` along the chosen fppf family.
Hom-descent is Lemma 95.7.2; object descent is `essSurj_ofArrows`. -/
theorem isStackFor_ofArrows {S : Scheme.{u}} {U : Over S}
    [IsPrestack.OnSite (Scheme.fppfTopology.over S) (p : Spaces S ⥤ Over S)]
    {I : Type v} [Small.{u} I] {Ui : I → Over S} (f : ∀ i, Ui i ⟶ U)
    (h_cover : Sieve.ofArrows Ui f ∈ Scheme.fppfTopology.over S U) :
    (Functor.fiberPseudofunctor (p : Spaces S ⥤ Over S)).IsStackFor
      (Presieve.ofArrows Ui f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
