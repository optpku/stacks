/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndZariski

@[expose] public section

universe u v w uA uB uC

namespace RingHom

namespace IndZariski.Raw

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- Composition of arbitrary-size ind-Zariski presentations. -/
theorem comp
    (f : A →+* B) (g : B →+* C)
    (hf : RingHom.IndZariski.Raw.{u, v, w} f)
    (hg : RingHom.IndZariski.Raw.{v, w, u} g) :
    RingHom.IndZariski.Raw.{u, w, v} (g.comp f) := sorry

end

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The comparison map between two ind-Zariski algebras over a common base
has an ind-Zariski presentation in any presentation universe. -/
theorem of_over_common_base
    (hA : RingHom.IndZariski.Raw.{u, v, uA} (algebraMap R A))
    (hB : RingHom.IndZariski.Raw.{u, w, uB} (algebraMap R B)) :
    RingHom.IndZariski.Raw.{v, w, uC} (algebraMap A B) := sorry

end

end IndZariski.Raw

namespace IndZariski

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

/-- A composite of ind-Zariski ring maps is ind-Zariski. -/
@[stacks 096Q "ind-Zariski composition"]
theorem comp (f : A →+* B) (g : B →+* C)
    (hf : f.IndZariski) (hg : g.IndZariski) :
    (g.comp f).IndZariski := sorry

/-- If `f` and `g.comp f` are ind-Zariski, then the comparison map `g` is
ind-Zariski. -/
theorem of_comp (f : A →+* B) (g : B →+* C)
    (hf : f.IndZariski) (hgf : (g.comp f).IndZariski) :
    g.IndZariski := sorry

end

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The algebra map between two ind-Zariski algebras over a common base is
ind-Zariski. -/
theorem of_over_common_base
    (hA : (algebraMap R A).IndZariski) (hB : (algebraMap R B).IndZariski) :
    (algebraMap A B).IndZariski := sorry

end

end IndZariski

end RingHom
