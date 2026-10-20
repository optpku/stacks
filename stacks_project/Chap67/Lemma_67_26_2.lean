/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Affine
public import ReasLib.RingTheory.Completion.Nagata
public import ReasLib.RingTheory.Normal.Nagata.Field
public import ReasLib.RingTheory.Normal.Nagata.Dedekind
public import Mathlib.Algebra.CharP.Algebra

/-!
# Ubiquity of Nagata algebraic spaces

Algebraic spaces locally of finite type over a Nagata scheme, a field, a Noetherian
complete local ring, `ℤ`, or a Dedekind ring of characteristic zero are Nagata.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    [Scheme.Nagata T.left] (f : X ⟶ ofOver T) [LocallyOfFiniteType f]

/- Lemma 67.26.2 (1): Any algebraic space locally of finite type over a Nagata scheme is
Nagata. -/
@[stacks 0BAV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata f :
    AlgebraicGeometry.AlgebraicSpace.IsNagata X)

end

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f]

-- Local instance justification (search instability): Canonical search fails on the displayed Over.mk projection; this section-only Prop instance forwards the existing affine-spectrum instance without adding an assumption.
local instance nagataFieldTarget : Scheme.Nagata (Over.mk σ).left :=
  AlgebraicGeometry.Scheme.instNagataSpec (CommRingCat.of k)

/- Lemma 67.26.2 (2): Any algebraic space locally of finite type over a field is Nagata. -/
@[stacks 0BAV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata f :
    AlgebraicGeometry.AlgebraicSpace.IsNagata X)

end

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    (σ : Spec (CommRingCat.of R) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f]

-- Local instance justification (search instability): Canonical search fails on the displayed Over.mk projection; this section-only Prop instance forwards the existing affine-spectrum instance without adding an assumption.
local instance nagataCompleteLocalTarget : Scheme.Nagata (Over.mk σ).left :=
  AlgebraicGeometry.Scheme.instNagataSpec (CommRingCat.of R)

/- Lemma 67.26.2 (3): Any algebraic space locally of finite type over a Noetherian complete
local ring is Nagata. -/
@[stacks 0BAV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata f :
    AlgebraicGeometry.AlgebraicSpace.IsNagata X)

end

section

variable {S : Scheme} {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of ℤ) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f]

-- Local instance justification (search instability): Canonical search fails on the displayed Over.mk projection; this section-only Prop instance forwards the existing affine-spectrum instance without adding an assumption.
local instance nagataIntTarget : Scheme.Nagata (Over.mk σ).left :=
  AlgebraicGeometry.Scheme.instNagataSpec (CommRingCat.of ℤ)

/- Lemma 67.26.2 (4): Any algebraic space locally of finite type over `ℤ` is Nagata. -/
@[stacks 0BAV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata f :
    AlgebraicGeometry.AlgebraicSpace.IsNagata X)

end

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {R : Type u}
    [CommRing R] [IsDedekindDomain R] [CharZero R]
    (σ : Spec (CommRingCat.of R) ⟶ S) (f : X ⟶ ofOver (Over.mk σ))
    [LocallyOfFiniteType f]

-- Local instance justification (search instability): Canonical search fails on the displayed Over.mk projection; this section-only Prop instance forwards the existing affine-spectrum instance without adding an assumption.
local instance nagataDedekindTarget : Scheme.Nagata (Over.mk σ).left :=
  AlgebraicGeometry.Scheme.instNagataSpec (CommRingCat.of R)

/- Lemma 67.26.2 (5): Any algebraic space locally of finite type over a Dedekind ring of
characteristic zero is Nagata. -/
@[stacks 0BAV] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isNagata f :
    AlgebraicGeometry.AlgebraicSpace.IsNagata X)

end

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
