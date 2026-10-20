/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Affine
import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.FiniteType
import ReasLib.RingTheory.Completion.Nagata
import ReasLib.RingTheory.Normal.Nagata.Dedekind
import ReasLib.RingTheory.Normal.Nagata.Field

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

section Field

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/- Lemma 29.18.2 (1): any scheme locally of finite type over a field is Nagata. -/
@[stacks 035B] #check (AlgebraicGeometry.Scheme.nagata_of_locallyOfFiniteType f :
  AlgebraicGeometry.Scheme.Nagata X)

end Field

section CompleteLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

/- Lemma 29.18.2 (2): any scheme locally of finite type over a Noetherian complete local ring is
Nagata. -/
@[stacks 035B] #check (AlgebraicGeometry.Scheme.nagata_of_locallyOfFiniteType f :
  AlgebraicGeometry.Scheme.Nagata X)

end CompleteLocalRing

section Integers

variable {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f]

/- Lemma 29.18.2 (3): any scheme locally of finite type over `Spec ℤ` is Nagata. -/
@[stacks 035B] #check (AlgebraicGeometry.Scheme.nagata_of_locallyOfFiniteType f :
  AlgebraicGeometry.Scheme.Nagata X)

end Integers

section DedekindDomain

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

/- Lemma 29.18.2 (4): any scheme locally of finite type over a Dedekind ring of characteristic
zero is Nagata. -/
@[stacks 035B] #check (AlgebraicGeometry.Scheme.nagata_of_locallyOfFiniteType f :
  AlgebraicGeometry.Scheme.Nagata X)

end DedekindDomain
