module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Criteria
import StacksCheckRecall

/-!
# A fiberwise criterion for morphisms representable by algebraic spaces

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces exactly when it is faithful on every fibre
and every fiber-pair isomorphism-class presheaf is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.2: let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Then `f` is representable by algebraic spaces if and only if
for each scheme `U / S` the fibre functor `fiberFunctor f U : X_U ⥤ Y_U` is
faithful, and for each `U` and each `y ∈ Ob(Y_U)` the presheaf of isomorphism
classes of pairs `(x, φ)` with `φ : h^* y ⟶ f(x)` on `Sch/U`, given by
`Hom.fiberPairClasses f y` after transport along `U.iteratedSliceEquiv` to
`Sch/U.left`, is an algebraic space over `U`. The source mentions a choice of
pullbacks for `Y`; that is the selected cleavage used by
`YonedaSlice.representative` in `Hom.fiberPairClasses`. -/
@[stacks 02ZY]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.iff_fiberwise :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f ↔
      (∀ U : Over S, (fiberFunctor f U).Faithful) ∧
        Hom.fiberPairClasses.isAlgebraicSpace f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.fiberwiseFaithful :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (U : Over S),
    (fiberFunctor f U).Faithful)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.fiberPairs :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    Hom.fiberPairClasses.isAlgebraicSpace f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_fiberwiseFaithful :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hFaithful : ∀ U : Over S, (fiberFunctor f U).Faithful)
    (hPairs : Hom.fiberPairClasses.isAlgebraicSpace f),
    relativelyRepresentableByAlgebraicSpaces f)

end AlgebraicGeometry
