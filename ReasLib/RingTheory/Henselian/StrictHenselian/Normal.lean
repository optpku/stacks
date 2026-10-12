/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Ideal.ResidueField.IsAlgClosed

@[expose] public section

universe u

namespace IsNormalRing

/-- A normal local ring with separably closed fraction field is strictly henselian. -/
instance strictHenselianLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalRing A]
    [IsSepClosed (FractionRing A)] : StrictHenselianLocalRing A := sorry

end IsNormalRing
