/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Branch
import StacksCheckRecall

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/- Lemma 37.36.4 (1): a smooth morphism preserves the number of geometric branches at a
point and its image. -/
@[stacks 0DQ2]
#check
  (AlgebraicGeometry.Smooth.geometricBranchNumberAt_eq :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
      (Xsh : Type v) [CommRing Xsh] [Algebra (X.presheaf.stalk x) Xsh]
      [IsStrictHenselizationOf (X.presheaf.stalk x) Xsh]
      (Ssh : Type w) [CommRing Ssh] [Algebra (S.presheaf.stalk (f x)) Ssh]
      [IsStrictHenselizationOf (S.presheaf.stalk (f x)) Ssh],
      X.geometricBranchNumberAt x Xsh = S.geometricBranchNumberAt (f x) Ssh)

/- Lemma 37.36.4 (2): if the residue-field extension at a point of a smooth morphism is
purely inseparable, then the morphism preserves the number of branches there. -/
@[stacks 0DQ2]
#check
  (AlgebraicGeometry.Smooth.branchNumberAt_eq_of_residuePurelyInseparable :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X),
      (f.residueFieldMap x).hom.IsPurelyInseparable →
      ∀ (Xh : Type v) [CommRing Xh] [Algebra (X.presheaf.stalk x) Xh]
        [IsHenselizationOf (X.presheaf.stalk x) Xh]
        (Sh : Type w) [CommRing Sh] [Algebra (S.presheaf.stalk (f x)) Sh]
        [IsHenselizationOf (S.presheaf.stalk (f x)) Sh],
        X.branchNumberAt x Xh = S.branchNumberAt (f x) Sh)

end AlgebraicGeometry
