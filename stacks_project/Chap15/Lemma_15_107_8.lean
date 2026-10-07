module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Branches.EssSmooth

/-!
@stack 0DQ1
-/

@[expose] public section

open IsLocalRing

universe u v w x

/- Lemma 15.107.8 (1), tag `0DQ1`: geometric branch number is invariant under a local
homomorphism that is a localization of a smooth ring map. -/
@[stacks 0DQ1 "Lemma 15.107.8 (1)"]
#check fun (A : Type u) (B : Type v) (Ash : Type w) (Bsh : Type x)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    (h : (algebraMap A B).EssSmooth) ↦
  (RingHom.EssSmooth.geometricBranchNumber_eq
    (A := A) (B := B) (Ash := Ash) (Bsh := Bsh) h :
    geometricBranchNumber A Ash = geometricBranchNumber B Bsh)

/- Lemma 15.107.8 (2), tag `0DQ1`: branch number is invariant when, in addition, the induced
residue-field map is purely inseparable. -/
@[stacks 0DQ1 "Lemma 15.107.8 (2)"]
#check fun (A : Type u) (B : Type v) (Ah : Type w) (Bh : Type x)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    (h : (algebraMap A B).EssSmooth)
    (hκ : (ResidueField.map (algebraMap A B)).IsPurelyInseparable) ↦
  (RingHom.EssSmooth.branchNumber_eq_of_residuePurelyInseparable
    (A := A) (B := B) (Ah := Ah) (Bh := Bh) h hκ :
    branchNumber A Ah = branchNumber B Bh)
