module

public import ReasLib.RingTheory.FiniteType.ArtinTate
import StacksCheckRecall

@[expose] public section

/-!
@stack 00IS
Lemma 10.51.7 (Artin-Tate), Stacks tag 00IS, is a source-facing formulation of the
canonical intermediate-subalgebra owner.  The reusable declaration is kept in ReasLib;
this chapter file only records the faithful type and the Mathlib primitive used by it.
-/

universe u v

@[stacks 00IS]
#check
  (@Subalgebra.finiteType_of_finite :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [IsNoetherianRing R] [Algebra.FiniteType R S]
      (T : Subalgebra R S) [Module.Finite T S], Algebra.FiniteType R T)

@[stacks 00IS "finitely generated scalar criterion"]
#check @fg_of_fg_of_fg
