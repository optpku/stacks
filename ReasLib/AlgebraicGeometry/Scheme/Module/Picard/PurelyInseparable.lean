/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FieldExtension
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension

/-- For a quasi-compact and quasi-separated scheme over a field of positive characteristic
whose canonical map to global sections is bijective, purely inseparable extension of scalars
bijects the prime-to-characteristic torsion subgroups of the Picard groups. -/
theorem picardPullback_bijOn_torsionBy
    (p : ℕ) [Fact p.Prime] {k k' : Type u}
    [Field k] [CharP k p] [Field k'] [Algebra k k'] [IsPurelyInseparable k k']
    (X : AlgebraicGeometry.SchemeOverField k) [CompactSpace X.left.carrier]
    [QuasiSeparatedSpace X.left.carrier]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (n : ℤ) (h_n : IsCoprime n (p : ℤ)) :
    Set.BijOn (Scheme.Hom.picardPullback (FieldExtension.toSource k k' X.hom))
      X.left.PicardGroup[n] (FieldExtension.baseChange k k' X.hom).PicardGroup[n] := sorry

end AlgebraicGeometry.FieldExtension
