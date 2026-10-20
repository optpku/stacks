module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.Basic
public import ReasLib.RingTheory.Etale.Weakly
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly etale localizations and filtered colimits

Weakly etale algebras include localizations and etale algebras, and are closed under filtered
colimits in the under-category over the fixed base ring.

@stack 092N
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace CommRingCat

/-- The morphism property on commutative rings whose arrows are weakly etale after installing the
algebra structure induced by the arrow. -/
@[stacks 092N "weakly etale morphism property"]
abbrev weaklyEtale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun {A B} [CommRing A] [CommRing B] (f : A →+* B) ↦
    letI : Algebra A B := f.toAlgebra
    Algebra.WeaklyEtale A B

end CommRingCat

namespace Algebra.WeaklyEtale

section Localization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.105.14 (1), Stacks `092N`: every localization is weakly etale over its source. -/
@[stacks 092N "(1), localizations are weakly etale"]
theorem of_isLocalization (M : Submonoid A) [IsLocalization M B] :
    Algebra.WeaklyEtale A B := sorry

/-- Lemma 15.105.14 (2), Stacks `092N`: every etale algebra is weakly etale.  This is the
explicit-witness companion to the canonical Mathlib instance. -/
@[stacks 092N "(2), etale algebras are weakly etale"]
theorem of_etale (h : Algebra.Etale A B) : Algebra.WeaklyEtale A B := sorry

end Localization

section FilteredColimit

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Type w} [Category.{w} J] [IsFiltered J]

/-- Lemma 15.105.14 (3), Stacks `092N`: a filtered colimit of weakly etale `A`-algebras is
weakly etale.  The colimit is taken in `Under (CommRingCat.of A)` and the displayed isomorphism
identifies its vertex with the target algebra `B`. -/
@[stacks 092N "(3), filtered colimits of weakly etale algebras"]
theorem of_isColimit
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap A B)))
    (hF : ∀ j, CommRingCat.weaklyEtale (F.obj j).hom) :
    Algebra.WeaklyEtale A B := sorry

end FilteredColimit

end Algebra.WeaklyEtale
