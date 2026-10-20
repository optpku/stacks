module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number

/-!
# Additivity of intersection numbers on algebraic spaces

Intersection numbers of invertible modules with a closed subspace proper over a
field are additive in each invertible factor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

/-- Replacing one member of a finite family of invertible modules by an invertible module
gives a family of invertible modules. -/
instance instIsInvertibleObject_update
    {S : Scheme.{u}} {X : AlgebraicSpace S} {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (idx : Fin d) (M : X.Modules) [isInvertibleObject M] :
    ∀ j : Fin d, isInvertibleObject (Function.update L idx M j) := sorry

section

-- Local instance justification (defeq pin): the imported intersection-number API elaborates HasInjectiveResolutions using Abelian-induced Preadditive and HasZeroMorphisms structures; this alignment makes the resolution binders and all three number applications use those same structures.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- If one factor in a family of invertible modules is isomorphic to a tensor product,
its intersection number with a closed subspace proper over a field is the sum of the
intersection numbers obtained by replacing that factor with each tensor factor. -/
theorem number_eq_add_of_iso_tensorObj {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
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

end

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
