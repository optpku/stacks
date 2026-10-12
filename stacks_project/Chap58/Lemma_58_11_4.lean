/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.StrictHenselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 58.11.4: for a normal local ring `A` with `X = Spec A`, a strict
henselization `Ash` of `A`, and fraction fields `K`, `Ksh` of `A` and `Ash`,
the sequence `π₁(Spec Ksh) → π₁(Spec K) → π₁(X) → 1` is exact in the sense of
Lemma 58.4.3 (1). -/
@[stacks 0BSM] #check (AlgebraicGeometry.Scheme.GeometricPoint.strictHenselizationExact :
    {A : Type u} → [CommRing A] → [IsLocalRing A] → [IsNormalRing A] →
    {Ash : Type u} → [CommRing Ash] → [Algebra A Ash] →
    [IsStrictHenselizationOf A Ash] → [IsDomain Ash] →
    (ηbar : GeometricPoint (Spec (CommRingCat.of (FractionRing Ash)))) →
    let iK :=
      Spec.map (CommRingCat.ofHom
        (IsFractionRing.map (K := FractionRing A) (L := FractionRing Ash)
          (j := algebraMap A Ash)
          (RingHom.FaithfullyFlat.injective
            (IsStrictHenselizationOf.faithfullyFlat (R := A) (S := Ash)))))
    let iX := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
    let h' := GeometricPoint.fundamentalGroupMap iK ηbar
    let h := GeometricPoint.fundamentalGroupMap iX (GeometricPoint.map ηbar iK)
    Function.Surjective h ∧
      h.comp h' = 1 ∧
      MonoidHom.ker h.toMonoidHom =
        (Subgroup.normalClosure
          (MonoidHom.range h'.toMonoidHom : Set _)).topologicalClosure)
