/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Stalk
public import ReasLib.RingTheory.LocalRing.Branches.EssSmooth

/-!
# Branch numbers under smooth morphisms

Smooth morphisms preserve geometric branch numbers. They also preserve ordinary branch numbers
when the induced residue-field extension is purely inseparable.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Smooth

/-- A smooth morphism preserves the geometric branch number at a point. -/
@[stacks 0DQ2]
theorem geometricBranchNumberAt_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (Xsh : Type v) [CommRing Xsh] [Algebra (X.presheaf.stalk x) Xsh]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Xsh]
    (Ssh : Type w) [CommRing Ssh] [Algebra (S.presheaf.stalk (f x)) Ssh]
    [IsStrictHenselizationOf (S.presheaf.stalk (f x)) Ssh] :
    X.geometricBranchNumberAt x Xsh = S.geometricBranchNumberAt (f x) Ssh := sorry

/-- A smooth morphism whose induced residue-field extension is purely inseparable preserves the
branch number at a point. -/
@[stacks 0DQ2]
theorem branchNumberAt_eq_of_residuePurelyInseparable
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (hκ : (f.residueFieldMap x).hom.IsPurelyInseparable)
    (Xh : Type v) [CommRing Xh] [Algebra (X.presheaf.stalk x) Xh]
    [IsHenselizationOf (X.presheaf.stalk x) Xh]
    (Sh : Type w) [CommRing Sh] [Algebra (S.presheaf.stalk (f x)) Sh]
    [IsHenselizationOf (S.presheaf.stalk (f x)) Sh] :
    X.branchNumberAt x Xh = S.branchNumberAt (f x) Sh := sorry

end AlgebraicGeometry.Smooth
