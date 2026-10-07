module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper scheme over a field of dimension at most one, the prime-to-characteristic
torsion in its Picard group has finrank at most the degree-one structure-sheaf cohomology
finrank plus its geometric genus. -/
theorem picardTorsionFinrank_le
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (h_prime_to_char : DVR.Field.PrimeToChar k ℓ) :
    @Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
        (AddSubgroup.torsionBy.zmodModule :
          Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) ≤
      Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 +
        GeometricGenus.ofScheme X hdim := sorry

end AlgebraicGeometry.SchemeOverField
