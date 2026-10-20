module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# Gerbes over a site

A gerbe over the site `(C, J)` is a stack in groupoids that is locally inhabited (every object
of the base admits a covering over which the gerbe has a section) and locally connected (any two
objects of the same fiber become isomorphic after restriction to a covering).

## Main declarations

* `CategoryTheory.IsGerbe` — the gerbe condition on a projection functor.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- Definition 8.11.1 (tag 06NZ): a gerbe over the site `(C, J)` is a stack in groupoids whose
presheaf of fiberwise isomorphism classes is locally terminal. This choice-independent owner
records local surjectivity and local injectivity of the canonical map to the terminal presheaf;
the source's coverwise inhabitedness and connectedness formulations are exposed by companion
theorems. -/
@[stacks 06NZ]
class IsGerbe (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends
      toStackInGroupoids : IsStack.InGroupoids J p,
      fiberClassesLocallySurjective : Presheaf.IsLocallySurjective J
        (terminal.from (Functor.fiberIsoClassPresheaf p)),
      fiberClassesLocallyInjective : Presheaf.IsLocallyInjective J
        (terminal.from (Functor.fiberIsoClassPresheaf p))

/- The parent class is the canonical owner, but its three projections are independently useful
   statement-level interfaces.  Keep their tags on the generated field declarations so a
   consumer searching for the local conditions finds the exact neutral API. -/
attribute [stacks 06NZ "gerbe stack-in-groupoids field"] IsGerbe.toStackInGroupoids
attribute [stacks 06NZ "gerbe locally-surjective fiber-class field"]
  IsGerbe.fiberClassesLocallySurjective
attribute [stacks 06NZ "gerbe locally-injective fiber-class field"]
  IsGerbe.fiberClassesLocallyInjective

/-- Every base object of a gerbe admits a covering over which the fiber has an object. This is
the source-facing coverwise form of local inhabitedness. -/
@[stacks 06NZ "gerbe local inhabitedness"]
theorem IsGerbe.locallyInhabited
    {J : GrothendieckTopology C} {p : S ⥤ C} [IsGerbe J p] (U : C) :
    ∃ T : J.Cover U, ∀ I : T.Arrow, Nonempty (p.Fiber I.Y) := sorry

/-- Two objects in one fiber of a gerbe become isomorphic after restriction to a covering. The
explicit cleavage appears only in this source-facing bridge. -/
@[stacks 06NZ "gerbe local connectedness"]
theorem IsGerbe.locallyIsomorphic
    {J : GrothendieckTopology C} {p : S ⥤ C} [IsGerbe J p]
    {U : C} (x y : p.Fiber U) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      Nonempty (I.f⁎[Functor.Cleavage.ofIsFibered p] x ≅
        I.f⁎[Functor.Cleavage.ofIsFibered p] y) := sorry

/-- For a projection already known to be a stack in groupoids, the gerbe condition is equivalent
to the two coverwise local conditions in the source definition. -/
@[stacks 06NZ "gerbe coverwise criterion"]
theorem IsGerbe.iff_coverwise
    {J : GrothendieckTopology C} {p : S ⥤ C}
    [IsStack.InGroupoids J p] :
    IsGerbe J p ↔
      (∀ U : C, ∃ T : J.Cover U,
        ∀ I : T.Arrow, Nonempty (p.Fiber I.Y)) ∧
      ∀ {U : C} (x y : p.Fiber U),
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          Nonempty (I.f⁎[Functor.Cleavage.ofIsFibered p] x ≅
            I.f⁎[Functor.Cleavage.ofIsFibered p] y) := sorry

/-- Construct a gerbe from the coverwise local inhabitedness and local connectedness conditions.
This is the source-facing introduction rule; the canonical owner remains the locally terminal
fiber-class presheaf encoded by `IsGerbe`. -/
@[stacks 06NZ "gerbe coverwise constructor"]
theorem IsGerbe.of_coverwise
    {J : GrothendieckTopology C} {p : S ⥤ C}
    [IsStack.InGroupoids J p]
    (h_inhabited : ∀ U : C,
      ∃ T : J.Cover U, ∀ I : T.Arrow, Nonempty (p.Fiber I.Y))
    (h_isomorphic : ∀ {U : C} (x y : p.Fiber U),
      ∃ T : J.Cover U, ∀ I : T.Arrow,
        Nonempty (I.f⁎[Functor.Cleavage.ofIsFibered p] x ≅
          I.f⁎[Functor.Cleavage.ofIsFibered p] y)) :
    IsGerbe J p := sorry

end CategoryTheory
