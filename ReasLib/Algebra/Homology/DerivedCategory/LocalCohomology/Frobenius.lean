module

public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.BaseChange

@[expose] public section

open CategoryTheory
open DerivedCategory.CechCompletion

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/-- If a prime `p` vanishes in a commutative ring `A` and `I` is finitely generated,
derived extension of local cohomology of `A` with support in `V(I)` along Frobenius
is isomorphic to that local cohomology itself. -/
theorem frobeniusBaseChangeIso {A : Type u} [CommRing A]
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (I : Ideal A) (hI : I.FG) :
    ∃ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
      ∃ (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ),
        Nonempty
          ((ModuleCat.derivedExtensionOfScalars (RingHom.frobeniusOfPrime p hp)).obj
              (RΓ.obj regular).obj ≅
            (RΓ.obj regular).obj) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
