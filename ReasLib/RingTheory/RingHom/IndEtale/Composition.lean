/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Composition for ind-etale ring maps

This leaf owns both ordinary composition and the comparison map between two
ind-etale algebras over a common base.
-/

universe u v w uA uB

namespace RingHom

namespace IndEtale.Raw

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- Composition of arbitrary-size ind-etale presentations. The input index
universes are independent of the ring universes. Finite-presentation descent
and flattening give an index universe bounded by their maximum. -/
theorem comp
    (f : A →+* B) (g : B →+* C)
    (hf : RingHom.IndEtale.Raw.{u, v, uA} f)
    (hg : RingHom.IndEtale.Raw.{v, w, uB} g) :
    RingHom.IndEtale.Raw.{u, w, max uA uB} (g.comp f) := sorry

end

end IndEtale.Raw

namespace IndEtale

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- A composite of ind-etale ring maps is ind-etale. -/
@[stacks 0BSI "ind-etale composition"]
theorem comp (f : A →+* B) (g : B →+* C)
    (hf : f.IndEtale) (hg : g.IndEtale) :
    (g.comp f).IndEtale := sorry

/-- If `f` and `g.comp f` are ind-etale, then the comparison map `g` is
ind-etale. -/
@[stacks 08HS "ind-etale comparison over a common base"]
theorem of_comp (f : A →+* B) (g : B →+* C)
    (hf : f.IndEtale) (hgf : (g.comp f).IndEtale) :
    g.IndEtale := sorry

end

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- Ind-etaleness transports along an algebra equivalence of targets. -/
theorem mapAlgEquiv (e : A ≃ₐ[R] B) (hA : (algebraMap R A).IndEtale) :
    (algebraMap R B).IndEtale := sorry

end

end IndEtale

namespace IndEtale

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- If `A` and `B` are ind-etale algebras over `R`, then `B` is ind-etale
over `A`. -/
theorem of_over_common_base
    (hA : (algebraMap R A).IndEtale)
    (hB : (algebraMap R B).IndEtale) :
    (algebraMap A B).IndEtale := sorry

end

end IndEtale

namespace IndEtale.Raw

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- An arbitrary-size ind-etale presentation transports along an algebra
equivalence of targets, keeping the same index universe. -/
theorem mapAlgEquiv (e : A ≃ₐ[R] B)
    (hA : RingHom.IndEtale.Raw.{u, u, uA} (algebraMap R A)) :
    RingHom.IndEtale.Raw.{u, u, uA} (algebraMap R B) := sorry

end

end IndEtale.Raw

namespace IndEtale.Raw

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- An arbitrary-size ind-etale presentation descends to the comparison map
between two ind-etale algebras over a common base. Choosing finite-stage
factorizations and their compatibility refinements bounds the index universe
by the maximum of the two input index universes. -/
theorem of_over_common_base
    (hA : RingHom.IndEtale.Raw.{u, v, uA} (algebraMap R A))
    (hB : RingHom.IndEtale.Raw.{u, w, uB} (algebraMap R B)) :
    RingHom.IndEtale.Raw.{v, w, max uA uB} (algebraMap A B) := sorry

end

end IndEtale.Raw

end RingHom
