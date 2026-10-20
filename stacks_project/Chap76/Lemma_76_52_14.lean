module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.GlobalSections

/-!
# Relative perfectness from perfect tensor-global sections

If `X` is separated, of finite presentation, and flat over a ring `A` and `K` is in
`D_QCoh(𝒪_X)`, then perfectness of `RΓ(X, E ⊗ᴸ K)` in `D(A)` for every perfect `E`
implies that `K` is `Spec(A)`-perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/- Lemma 76.52.14. Let `A` be a ring. Let `X` be an algebraic space separated, of
finite presentation, and flat over `A`. Let `K` in `D_QCoh(𝒪_X)`. If `RΓ(X, E ⊗ᴸ K)`
is perfect in `D(A)` for every perfect `E` in `D(𝒪_X)`, then `K` is `Spec(A)`-perfect. -/
@[stacks 0GFL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPerfectRelativeTo_of_globalSectionsTensor :
    ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Separated (SchemeRealization.toBase X)]
    [FinitePresentation (SchemeRealization.toBase X)]
    [Flat (SchemeRealization.toBase X)]
    {K : ModuleDerived X} (hK : derivedQuasiCoherentModuleProperty X K)
    (h : ∀ E : ModuleDerived X, IsPerfect E →
      DerivedCategory.IsPerfect
        ((Modules.globalSectionsOver (SchemeRealization.toBase X)).obj (E ⊗ᴸ K))),
    IsPerfectRelativeTo (SchemeRealization.toBase X) K)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
