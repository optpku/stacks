module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module properties on principal-open covers

Mathlib supplies the elementwise localization criteria and the locality of finite
presentation.  This leaf adds the two direct interfaces needed most often by downstream
arguments: detecting the zero module and detecting a short exact sequence.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A module is a subsingleton when it is a subsingleton on a family of principal opens whose
denominators generate the unit ideal.  The cover may be infinite. -/
@[stacks 00EO "zero modules on a principal-open cover"]
theorem subsingleton_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ f : s, Subsingleton (LocalizedModule.Away f.1 M)) :
    Subsingleton M := sorry

end Module

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R]

/-- A short complex of modules is short exact when its restriction to every member of a
principal-open cover is short exact.  The cover may be infinite. -/
@[stacks 00EO "short exactness on a principal-open cover"]
theorem of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (S : CategoryTheory.ShortComplex (ModuleCat.{max u v} R))
    (h : ∀ f : s,
      (S.map (ModuleCat.localizedModuleFunctor (Submonoid.powers f.1))).ShortExact) :
    S.ShortExact := sorry

end CategoryTheory.ShortComplex.ShortExact
