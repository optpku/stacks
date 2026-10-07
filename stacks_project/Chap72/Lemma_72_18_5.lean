module

public import stacks_project.Chap72.Definition_72_18_3_Number

/-!
# Lemma 72.18.5

The intersection number of invertible modules with a closed subspace proper over
a field is additive in each invertible factor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- If every member of a finite family of modules is invertible and `M` is invertible, then the
family obtained by replacing one factor with `M` is invertible. -/
instance instIsInvertibleObject_update
    {S : Scheme.{u}} {X : AlgebraicSpace S} {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (idx : Fin d) (M : X.Modules) [isInvertibleObject M] :
    ∀ j : Fin d, isInvertibleObject (Function.update L idx M j) := sorry

/-- Lemma 72.18.5: in the situation of Definition 72.18.3, the intersection number
`(L 0 ⋯ L (d - 1) · Z)` is additive in each invertible factor. If
`L idx ≅ tensorObj L' L''`, then
`(L 0 ⋯ L idx ⋯ L (d - 1) · Z) =
(L 0 ⋯ L' ⋯ L (d - 1) · Z) + (L 0 ⋯ L'' ⋯ L (d - 1) · Z)`. -/
@[stacks 0EDH]
theorem number_eq_add_of_iso_tensorObj {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (idx : Fin d) (L' L'' : X.Modules)
    [isInvertibleObject L'] [isInvertibleObject L'']
    (hTensor : L idx ≅ tensorObj L' L'') :
    number i hZdim L =
      number i hZdim (Function.update L idx L') +
        number i hZdim (Function.update L idx L'') := sorry

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
