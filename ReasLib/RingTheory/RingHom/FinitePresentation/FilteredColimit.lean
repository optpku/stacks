module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation and filtered colimits

This leaf records the reusable categorical characterization of finitely
presented commutative-ring maps.  Mathlib owns the forward preservation
theorem; the converse and the stagewise factorization formulation belong here
because they are useful independently of the Chapter 10 presentation.

@stack 00QO
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace RingHom.FinitePresentation

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Stacks `00QO`: every morphism from the `R`-algebra presented by `f` to a
filtered colimit of `R`-algebras factors through one stage. -/
@[stacks 00QO "filtered-colimit factorization"]
def filteredColimitFactorization (f : R →+* S) : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (_ : IsColimit c)
    (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
      ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j),
        g = g' ≫ c.ι.app j

/-- Stacks `00QO`: preservation of filtered colimits by the represented
functor implies the stagewise factorization property. -/
@[stacks 00QO "filtered-colimit factorization"]
theorem factorization_of_preservesFilteredColimits (f : R →+* S)
    (h : PreservesFilteredColimits
      (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f))))) :
    filteredColimitFactorization f := sorry

/-- Stacks `00QO`: a commutative-ring map is of finite presentation exactly
when its represented functor preserves filtered colimits. -/
@[stacks 00QO "finite presentation and filtered colimits"]
theorem iff_preservesFilteredColimits (f : R →+* S) :
    f.FinitePresentation ↔
      PreservesFilteredColimits
        (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))) := sorry

/-- Stacks `00QO`: a commutative-ring map is of finite presentation exactly
when it has the filtered-colimit stagewise factorization property. -/
@[stacks 00QO "finite presentation and factorization"]
theorem iff_filteredColimitFactorization (f : R →+* S) :
    f.FinitePresentation ↔ filteredColimitFactorization f := sorry

/-- Stacks `00QO`: finite presentation, preservation of filtered colimits by
the represented functor, and stagewise filtered-colimit factorization are
equivalent for a commutative-ring map. -/
@[stacks 00QO]
theorem tfae (f : R →+* S) :
    List.TFAE
      [f.FinitePresentation,
        PreservesFilteredColimits
          (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))),
        filteredColimitFactorization f] := sorry

end RingHom.FinitePresentation
