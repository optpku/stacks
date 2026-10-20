module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.DenseOpen
import StacksCheckRecall

/-!
# Extending local finite presentation from a dense open of algebraic spaces

A morphism of algebraic spaces that is locally of finite type and flat is
locally of finite presentation if its restriction to a quasi-compact
scheme-theoretically dense open of the target is locally of finite
presentation.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.37.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `V ⟶ Y` be an open subspace. Assume `f` is
locally of finite type and flat, `V ⟶ Y` is quasi-compact and
scheme-theoretically dense, and the restriction to the inverse image of `V`
is locally of finite presentation. Then `f` is locally of finite
presentation. -/
@[stacks 0877] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.of_restrict_of_flat :
    ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y),
      LocallyOfFiniteType f → Flat f → ∀ (ι : V ⟶ Y),
        (h_open : Representable.IsOpenImmersion ι) →
        Representable.QuasiCompact ι → Open.IsSchemeTheoreticallyDense ι →
        LocallyOfFinitePresentation (Open.inverseImageTo f ι h_open) →
        LocallyOfFinitePresentation f)
