module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.GlobalSections
import StacksCheckRecall

/-!
# Relative pseudo-coherence from perfect tensor-global sections

If `X` is separated of finite presentation over a ring `A` and `K` is in
`D_QCoh(𝒪_X)`, then pseudo-coherence of `RΓ(X, E ⊗ᴸ K)` in `D(A)` for every
perfect `E` implies that `K` is pseudo-coherent relative to `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 76.51.5. Let `A` be a ring. Let `X` be an algebraic space separated and of
finite presentation over `A`. Let `K` in `D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗ᴸ K)` is
pseudo-coherent in `D(A)` for every perfect `E` in `D(𝒪_X)`, then `K` is
pseudo-coherent relative to `A`. -/
@[stacks 0GFJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isPseudoCoherentOver_of_globalSectionsTensor_perfect :
    ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)] (K : DerivedQCoh X),
    (∀ E : ModuleDerived X, ModuleDerived.IsPerfect E →
      CategoryTheory.DerivedCategory.IsPseudoCoherent
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K.obj))) →
    ModuleDerived.IsPseudoCoherentOver (SchemeRealization.toBase X) K.obj)
