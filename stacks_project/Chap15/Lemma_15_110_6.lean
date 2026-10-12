/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal.GeometricNormal

/-!
# Lemma 15.110.6

@stack 0C2F
-/

@[expose] public section

universe u v w

/- Lemma 15.110.6 (current Stacks numbering: Lemma 15.111.6, tag `0C2F`):
geometrically normal formal fibers imply universal catenarity after Henselization,
and imply universal catenarity of the base in the unibranch case. -/

/- Lemma 15.110.6 (1), tag `0C2F`: universal catenarity of a chosen Henselization. -/
@[stacks 0C2F "Lemma 15.110.6 (1)"]
#check fun (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) ↦
  (UniversallyCatenaryRing.of_henselization (A := A) (Ah := Ah) hgeom :
    UniversallyCatenaryRing.{v, w} Ah)

/- Lemma 15.110.6 (2), tag `0C2F`: universal catenarity in the unibranch case. -/
@[stacks 0C2F "Lemma 15.110.6 (2)"]
#check fun (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsUnibranch A]
    (hgeom :
      (FieldAlgebraProperty.geometricallyNormal).HoldsOnFormalFibers A) ↦
  (UniversallyCatenaryRing.of_unibranch (A := A) hgeom :
    UniversallyCatenaryRing.{u, w} A)
