/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying ring (pre)sheaves

This file supplies the functorial passage from commutative-ring-valued (pre)sheaves to
ring-valued ones on an arbitrary site.  It is deliberately independent of `TopCat` and of module
sheaves, so those layers can share one canonical conversion owner.
-/

@[expose] public section

open CategoryTheory

universe r u v w

namespace CategoryTheory.Presheaf

variable {C : Type v} [Category.{w} C]

/-- The underlying possibly noncommutative ring presheaf of a commutative-ring-valued
presheaf. -/
abbrev ringPresheafOfComm (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Cᵒᵖ ⥤ RingCat.{u} :=
  𝒪 ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The morphism of underlying ring presheaves induced by a morphism of commutative-ring
presheaves. -/
abbrev ringPresheafOfCommMap
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    ringPresheafOfComm 𝒪₁ ⟶ ringPresheafOfComm 𝒪₂ :=
  Functor.whiskerRight p (forget₂ CommRingCat.{u} RingCat.{u})

end CategoryTheory.Presheaf

namespace CategoryTheory.Presheaf.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type v} [Category.{w} C]

/-- The underlying commutative-ring presheaf of a commutative `R`-algebra-valued presheaf. -/
@[stacks 0CS6 "underlying commutative-ring presheaf of an algebra presheaf"]
abbrev commRing
    (𝒪 : Cᵒᵖ ⥤ CommAlgCat.{u} R) : Cᵒᵖ ⥤ CommRingCat.{u} :=
  𝒪 ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

/-- The underlying ring presheaf of a commutative `R`-algebra-valued presheaf. -/
@[stacks 0CS6 "underlying ring presheaf of an algebra presheaf"]
abbrev ring
    (𝒪 : Cᵒᵖ ⥤ CommAlgCat.{u} R) : Cᵒᵖ ⥤ RingCat.{u} :=
  _root_.CategoryTheory.Presheaf.ringPresheafOfComm (commRing 𝒪)

/-- A morphism of commutative `R`-algebra presheaves induces a morphism of their underlying
commutative-ring presheaves. -/
@[stacks 0CS6 "underlying commutative-ring map of algebra presheaves"]
abbrev commRingMap
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommAlgCat.{u} R} (p : 𝒪₁ ⟶ 𝒪₂) :
    commRing 𝒪₁ ⟶ commRing 𝒪₂ :=
  Functor.whiskerRight p (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})

/-- A morphism of commutative `R`-algebra presheaves induces a morphism of their underlying ring
presheaves. -/
@[stacks 0CS6 "underlying ring map of algebra presheaves"]
abbrev ringMap
    {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommAlgCat.{u} R} (p : 𝒪₁ ⟶ 𝒪₂) :
    ring 𝒪₁ ⟶ ring 𝒪₂ :=
  _root_.CategoryTheory.Presheaf.ringPresheafOfCommMap (commRingMap p)

end CategoryTheory.Presheaf.CommAlg

namespace CategoryTheory.Sheaf

variable {C : Type v} [Category.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The underlying possibly noncommutative ring sheaf of a commutative-ring-valued sheaf on an
arbitrary site. -/
abbrev ringSheafOfComm (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj 𝒪

/-- The morphism of underlying ring sheaves induced by a morphism of commutative-ring sheaves on
an arbitrary site. -/
abbrev ringSheafOfCommMap
    {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂) :
    ringSheafOfComm 𝒪₁ ⟶ ringSheafOfComm 𝒪₂ :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map p

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type v} [Category.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})]

/-- The underlying commutative-ring sheaf of a commutative `R`-algebra-valued sheaf.  This
conversion preserves the algebra-valued sheaf as its canonical data owner; it only exposes the
ring presentation needed by existing ringed-site constructions. -/
@[stacks 0CS6 "underlying commutative-ring sheaf of an algebra sheaf"]
abbrev commRing
    (𝒪 : Sheaf J (CommAlgCat.{u} R)) : Sheaf J CommRingCat.{u} :=
  (sheafCompose J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})).obj 𝒪

/-- A morphism of commutative `R`-algebra sheaves induces a morphism of their underlying
commutative-ring sheaves. -/
@[stacks 0CS6 "underlying commutative-ring map of algebra sheaves"]
abbrev commRingMap
    {𝒪₁ 𝒪₂ : Sheaf J (CommAlgCat.{u} R)} (p : 𝒪₁ ⟶ 𝒪₂) :
    commRing 𝒪₁ ⟶ commRing 𝒪₂ :=
  (sheafCompose J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})).map p

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The underlying ring sheaf of a commutative `R`-algebra-valued sheaf.  The result deliberately
forgets the `R`-action; coefficient-linear constructions should retain the original
`CommAlgCat R`-valued sheaf alongside this presentation. -/
@[stacks 0CS6 "underlying ring sheaf of an algebra sheaf"]
abbrev ring
    (𝒪 : Sheaf J (CommAlgCat.{u} R)) : Sheaf J RingCat.{u} :=
  _root_.CategoryTheory.Sheaf.ringSheafOfComm (commRing 𝒪)

/-- A morphism of commutative `R`-algebra sheaves induces a morphism of their underlying ring
sheaves. -/
@[stacks 0CS6 "underlying ring map of algebra sheaves"]
abbrev ringMap
    {𝒪₁ 𝒪₂ : Sheaf J (CommAlgCat.{u} R)} (p : 𝒪₁ ⟶ 𝒪₂) :
    ring 𝒪₁ ⟶ ring 𝒪₂ :=
  _root_.CategoryTheory.Sheaf.ringSheafOfCommMap (commRingMap p)

end CategoryTheory.Sheaf.CommAlg
